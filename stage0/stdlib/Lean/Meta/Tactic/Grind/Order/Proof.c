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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0;
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
lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object* v_declName_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Grind_Order_getOrder(v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_30_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_30_ == 0)
{
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_30_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_30_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_type_19_; lean_object* v_u_20_; lean_object* v_isPreorderInst_21_; lean_object* v_leInst_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v_type_19_ = lean_ctor_get(v_a_15_, 1);
lean_inc_ref(v_type_19_);
v_u_20_ = lean_ctor_get(v_a_15_, 2);
lean_inc(v_u_20_);
v_isPreorderInst_21_ = lean_ctor_get(v_a_15_, 3);
lean_inc_ref(v_isPreorderInst_21_);
v_leInst_22_ = lean_ctor_get(v_a_15_, 4);
lean_inc_ref(v_leInst_22_);
lean_dec(v_a_15_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v_u_20_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = l_Lean_mkConst(v_declName_1_, v___x_24_);
v___x_26_ = l_Lean_mkApp3(v___x_25_, v_type_19_, v_leInst_22_, v_isPreorderInst_21_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_26_);
v___x_28_ = v___x_17_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
lean_dec(v_declName_1_);
v_a_31_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_14_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_14_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkLePreorderPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v_declName_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix___boxed(lean_object* v_declName_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v_declName_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec(v_a_42_);
lean_dec(v_a_41_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(lean_object* v_msg_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = l_Lean_instInhabitedExpr;
v___x_56_ = lean_panic_fn_borrowed(v___x_55_, v_msg_54_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2));
v___x_61_ = lean_unsigned_to_nat(14u);
v___x_62_ = lean_unsigned_to_nat(22u);
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1));
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0));
v___x_65_ = l_mkPanicMessageWithDecl(v___x_64_, v___x_63_, v___x_62_, v___x_61_, v___x_60_);
return v___x_65_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(lean_object* v_declName_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_Order_getOrder(v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_100_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_100_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_100_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_100_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v_type_84_; lean_object* v_u_85_; lean_object* v_leInst_86_; lean_object* v_isPartialInst_x3f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___y_92_; 
v_type_84_ = lean_ctor_get(v_a_80_, 1);
lean_inc_ref(v_type_84_);
v_u_85_ = lean_ctor_get(v_a_80_, 2);
lean_inc(v_u_85_);
v_leInst_86_ = lean_ctor_get(v_a_80_, 4);
lean_inc_ref(v_leInst_86_);
v_isPartialInst_x3f_87_ = lean_ctor_get(v_a_80_, 6);
lean_inc(v_isPartialInst_x3f_87_);
lean_dec(v_a_80_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v_u_85_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_mkConst(v_declName_66_, v___x_89_);
if (lean_obj_tag(v_isPartialInst_x3f_87_) == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_98_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_97_);
v___y_92_ = v___x_98_;
goto v___jp_91_;
}
else
{
lean_object* v_val_99_; 
v_val_99_ = lean_ctor_get(v_isPartialInst_x3f_87_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v_isPartialInst_x3f_87_, 1);
v___y_92_ = v_val_99_;
goto v___jp_91_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = l_Lean_mkApp3(v___x_90_, v_type_84_, v_leInst_86_, v___y_92_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_93_);
v___x_95_ = v___x_82_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
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
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec(v_declName_66_);
v_a_101_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_79_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_79_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_66_ = stack[0].m_obj;
lean_object* v_a_67_ = stack[1].m_obj;
lean_object* v_a_68_ = stack[2].m_obj;
lean_object* v_a_69_ = stack[3].m_obj;
lean_object* v_a_70_ = stack[4].m_obj;
lean_object* v_a_71_ = stack[5].m_obj;
lean_object* v_a_72_ = stack[6].m_obj;
lean_object* v_a_73_ = stack[7].m_obj;
lean_object* v_a_74_ = stack[8].m_obj;
lean_object* v_a_75_ = stack[9].m_obj;
lean_object* v_a_76_ = stack[10].m_obj;
lean_object* v_a_77_ = stack[11].m_obj;
lean_object* v_res_109_;
v_res_109_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v_declName_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___boxed(lean_object* v_declName_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v_declName_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec(v_a_112_);
lean_dec(v_a_111_);
return v_res_123_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(lean_object* v_declName_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Grind_Order_getOrder(v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_165_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_165_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_165_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_165_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_type_142_; lean_object* v_u_143_; lean_object* v_leInst_144_; lean_object* v_ltInst_x3f_145_; lean_object* v_lawfulOrderLTInst_x3f_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_158_; 
v_type_142_ = lean_ctor_get(v_a_138_, 1);
lean_inc_ref(v_type_142_);
v_u_143_ = lean_ctor_get(v_a_138_, 2);
lean_inc(v_u_143_);
v_leInst_144_ = lean_ctor_get(v_a_138_, 4);
lean_inc_ref(v_leInst_144_);
v_ltInst_x3f_145_ = lean_ctor_get(v_a_138_, 5);
lean_inc(v_ltInst_x3f_145_);
v_lawfulOrderLTInst_x3f_146_ = lean_ctor_get(v_a_138_, 8);
lean_inc(v_lawfulOrderLTInst_x3f_146_);
lean_dec(v_a_138_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v_u_143_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_Lean_mkConst(v_declName_124_, v___x_148_);
if (lean_obj_tag(v_ltInst_x3f_145_) == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_163_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_162_);
v___y_158_ = v___x_163_;
goto v___jp_157_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v_ltInst_x3f_145_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v_ltInst_x3f_145_, 1);
v___y_158_ = v_val_164_;
goto v___jp_157_;
}
v___jp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = l_Lean_mkApp4(v___x_149_, v_type_142_, v_leInst_144_, v___y_151_, v___y_152_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_153_);
v___x_155_ = v___x_140_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
v___jp_157_:
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_146_) == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_160_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_159_);
v___y_151_ = v___y_158_;
v___y_152_ = v___x_160_;
goto v___jp_150_;
}
else
{
lean_object* v_val_161_; 
v_val_161_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_146_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_146_, 1);
v___y_151_ = v___y_158_;
v___y_152_ = v_val_161_;
goto v___jp_150_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec(v_declName_124_);
v_a_166_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_137_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_137_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_124_ = stack[0].m_obj;
lean_object* v_a_125_ = stack[1].m_obj;
lean_object* v_a_126_ = stack[2].m_obj;
lean_object* v_a_127_ = stack[3].m_obj;
lean_object* v_a_128_ = stack[4].m_obj;
lean_object* v_a_129_ = stack[5].m_obj;
lean_object* v_a_130_ = stack[6].m_obj;
lean_object* v_a_131_ = stack[7].m_obj;
lean_object* v_a_132_ = stack[8].m_obj;
lean_object* v_a_133_ = stack[9].m_obj;
lean_object* v_a_134_ = stack[10].m_obj;
lean_object* v_a_135_ = stack[11].m_obj;
lean_object* v_res_174_;
v_res_174_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix___boxed(lean_object* v_declName_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec(v_a_177_);
lean_dec(v_a_176_);
return v_res_188_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(lean_object* v_declName_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Meta_Grind_Order_getOrder(v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_204_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_214_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_214_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_isPreorderInst_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v_isPreorderInst_209_ = lean_ctor_get(v_a_203_, 3);
lean_inc_ref(v_isPreorderInst_209_);
lean_dec(v_a_203_);
v___x_210_ = l_Lean_Expr_app___override(v_a_205_, v_isPreorderInst_209_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_212_ = v___x_207_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_dec(v_a_203_);
return v___x_204_;
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_declName_189_);
v_a_215_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_202_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_202_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_189_ = stack[0].m_obj;
lean_object* v_a_190_ = stack[1].m_obj;
lean_object* v_a_191_ = stack[2].m_obj;
lean_object* v_a_192_ = stack[3].m_obj;
lean_object* v_a_193_ = stack[4].m_obj;
lean_object* v_a_194_ = stack[5].m_obj;
lean_object* v_a_195_ = stack[6].m_obj;
lean_object* v_a_196_ = stack[7].m_obj;
lean_object* v_a_197_ = stack[8].m_obj;
lean_object* v_a_198_ = stack[9].m_obj;
lean_object* v_a_199_ = stack[10].m_obj;
lean_object* v_a_200_ = stack[11].m_obj;
lean_object* v_res_223_;
v_res_223_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix___boxed(lean_object* v_declName_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec(v_a_226_);
lean_dec(v_a_225_);
return v_res_237_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(lean_object* v_declName_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Meta_Grind_Order_getOrder(v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_253_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_268_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_268_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_268_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_268_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___y_259_; lean_object* v_isLinearPreInst_x3f_264_; 
v_isLinearPreInst_x3f_264_ = lean_ctor_get(v_a_252_, 7);
lean_inc(v_isLinearPreInst_x3f_264_);
lean_dec(v_a_252_);
if (lean_obj_tag(v_isLinearPreInst_x3f_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_266_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_265_);
v___y_259_ = v___x_266_;
goto v___jp_258_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v_isLinearPreInst_x3f_264_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_isLinearPreInst_x3f_264_, 1);
v___y_259_ = v_val_267_;
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = l_Lean_Expr_app___override(v_a_254_, v___y_259_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_260_);
v___x_262_ = v___x_256_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_dec(v_a_252_);
return v___x_253_;
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_declName_238_);
v_a_269_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_251_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_251_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_238_ = stack[0].m_obj;
lean_object* v_a_239_ = stack[1].m_obj;
lean_object* v_a_240_ = stack[2].m_obj;
lean_object* v_a_241_ = stack[3].m_obj;
lean_object* v_a_242_ = stack[4].m_obj;
lean_object* v_a_243_ = stack[5].m_obj;
lean_object* v_a_244_ = stack[6].m_obj;
lean_object* v_a_245_ = stack[7].m_obj;
lean_object* v_a_246_ = stack[8].m_obj;
lean_object* v_a_247_ = stack[9].m_obj;
lean_object* v_a_248_ = stack[10].m_obj;
lean_object* v_a_249_ = stack[11].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v_declName_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix___boxed(lean_object* v_declName_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v_declName_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec(v_a_280_);
lean_dec(v_a_279_);
return v_res_291_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix(lean_object* v_declName_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Grind_Order_getOrder(v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_326_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_326_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_326_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_326_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_type_310_; lean_object* v_u_311_; lean_object* v_leInst_312_; lean_object* v_isLinearPreInst_x3f_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___y_318_; 
v_type_310_ = lean_ctor_get(v_a_306_, 1);
lean_inc_ref(v_type_310_);
v_u_311_ = lean_ctor_get(v_a_306_, 2);
lean_inc(v_u_311_);
v_leInst_312_ = lean_ctor_get(v_a_306_, 4);
lean_inc_ref(v_leInst_312_);
v_isLinearPreInst_x3f_313_ = lean_ctor_get(v_a_306_, 7);
lean_inc(v_isLinearPreInst_x3f_313_);
lean_dec(v_a_306_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_u_311_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = l_Lean_mkConst(v_declName_292_, v___x_315_);
if (lean_obj_tag(v_isLinearPreInst_x3f_313_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_324_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_323_);
v___y_318_ = v___x_324_;
goto v___jp_317_;
}
else
{
lean_object* v_val_325_; 
v_val_325_ = lean_ctor_get(v_isLinearPreInst_x3f_313_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_isLinearPreInst_x3f_313_, 1);
v___y_318_ = v_val_325_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = l_Lean_mkApp3(v___x_316_, v_type_310_, v_leInst_312_, v___y_318_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_319_);
v___x_321_ = v___x_308_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_declName_292_);
v_a_327_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_305_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_305_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkLeLinearPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_292_ = stack[0].m_obj;
lean_object* v_a_293_ = stack[1].m_obj;
lean_object* v_a_294_ = stack[2].m_obj;
lean_object* v_a_295_ = stack[3].m_obj;
lean_object* v_a_296_ = stack[4].m_obj;
lean_object* v_a_297_ = stack[5].m_obj;
lean_object* v_a_298_ = stack[6].m_obj;
lean_object* v_a_299_ = stack[7].m_obj;
lean_object* v_a_300_ = stack[8].m_obj;
lean_object* v_a_301_ = stack[9].m_obj;
lean_object* v_a_302_ = stack[10].m_obj;
lean_object* v_a_303_ = stack[11].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v_declName_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix___boxed(lean_object* v_declName_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v_declName_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec(v_a_338_);
lean_dec(v_a_337_);
return v_res_349_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object* v_declName_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_Grind_Order_getOrder(v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_387_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_387_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v_ringInst_x3f_377_; lean_object* v_orderedRingInst_x3f_378_; lean_object* v___y_380_; 
v_ringInst_x3f_377_ = lean_ctor_get(v_a_364_, 11);
lean_inc(v_ringInst_x3f_377_);
v_orderedRingInst_x3f_378_ = lean_ctor_get(v_a_364_, 12);
lean_inc(v_orderedRingInst_x3f_378_);
lean_dec(v_a_364_);
if (lean_obj_tag(v_ringInst_x3f_377_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_385_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_384_);
v___y_380_ = v___x_385_;
goto v___jp_379_;
}
else
{
lean_object* v_val_386_; 
v_val_386_ = lean_ctor_get(v_ringInst_x3f_377_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v_ringInst_x3f_377_, 1);
v___y_380_ = v_val_386_;
goto v___jp_379_;
}
v___jp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = l_Lean_mkAppB(v_a_366_, v___y_371_, v___y_372_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_373_);
v___x_375_ = v___x_368_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
v___jp_379_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_378_) == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_382_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_381_);
v___y_371_ = v___y_380_;
v___y_372_ = v___x_382_;
goto v___jp_370_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v_orderedRingInst_x3f_378_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_orderedRingInst_x3f_378_, 1);
v___y_371_ = v___y_380_;
v___y_372_ = v_val_383_;
goto v___jp_370_;
}
}
}
}
else
{
lean_dec(v_a_364_);
return v___x_365_;
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_declName_350_);
v_a_388_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_363_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_363_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkOrdRingPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_350_ = stack[0].m_obj;
lean_object* v_a_351_ = stack[1].m_obj;
lean_object* v_a_352_ = stack[2].m_obj;
lean_object* v_a_353_ = stack[3].m_obj;
lean_object* v_a_354_ = stack[4].m_obj;
lean_object* v_a_355_ = stack[5].m_obj;
lean_object* v_a_356_ = stack[6].m_obj;
lean_object* v_a_357_ = stack[7].m_obj;
lean_object* v_a_358_ = stack[8].m_obj;
lean_object* v_a_359_ = stack[9].m_obj;
lean_object* v_a_360_ = stack[10].m_obj;
lean_object* v_a_361_ = stack[11].m_obj;
lean_object* v_res_396_;
v_res_396_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v_declName_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
stack->m_obj
 = v_res_396_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix___boxed(lean_object* v_declName_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v_declName_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec(v_a_399_);
lean_dec(v_a_398_);
return v_res_410_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(lean_object* v_declName_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Order_getOrder(v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v_declName_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_448_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_448_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v_ringInst_x3f_438_; lean_object* v_orderedRingInst_x3f_439_; lean_object* v___y_441_; 
v_ringInst_x3f_438_ = lean_ctor_get(v_a_425_, 11);
lean_inc(v_ringInst_x3f_438_);
v_orderedRingInst_x3f_439_ = lean_ctor_get(v_a_425_, 12);
lean_inc(v_orderedRingInst_x3f_439_);
lean_dec(v_a_425_);
if (lean_obj_tag(v_ringInst_x3f_438_) == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_446_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_445_);
v___y_441_ = v___x_446_;
goto v___jp_440_;
}
else
{
lean_object* v_val_447_; 
v_val_447_ = lean_ctor_get(v_ringInst_x3f_438_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_ringInst_x3f_438_, 1);
v___y_441_ = v_val_447_;
goto v___jp_440_;
}
v___jp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_mkAppB(v_a_427_, v___y_432_, v___y_433_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_434_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
v___jp_440_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_439_) == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_443_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_442_);
v___y_432_ = v___y_441_;
v___y_433_ = v___x_443_;
goto v___jp_431_;
}
else
{
lean_object* v_val_444_; 
v_val_444_ = lean_ctor_get(v_orderedRingInst_x3f_439_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_orderedRingInst_x3f_439_, 1);
v___y_432_ = v___y_441_;
v___y_433_ = v_val_444_;
goto v___jp_431_;
}
}
}
}
else
{
lean_dec(v_a_425_);
return v___x_426_;
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_declName_411_);
v_a_449_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_424_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_424_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_411_ = stack[0].m_obj;
lean_object* v_a_412_ = stack[1].m_obj;
lean_object* v_a_413_ = stack[2].m_obj;
lean_object* v_a_414_ = stack[3].m_obj;
lean_object* v_a_415_ = stack[4].m_obj;
lean_object* v_a_416_ = stack[5].m_obj;
lean_object* v_a_417_ = stack[6].m_obj;
lean_object* v_a_418_ = stack[7].m_obj;
lean_object* v_a_419_ = stack[8].m_obj;
lean_object* v_a_420_ = stack[9].m_obj;
lean_object* v_a_421_ = stack[10].m_obj;
lean_object* v_a_422_ = stack[11].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v_declName_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix___boxed(lean_object* v_declName_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v_declName_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec(v_a_460_);
lean_dec(v_a_459_);
return v_res_471_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(lean_object* v_u_499_, lean_object* v_v_500_, lean_object* v_w_501_, uint8_t v_strict_u2081_502_, uint8_t v_strict_u2082_503_, lean_object* v_h_u2081_504_, lean_object* v_h_u2082_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_h_519_; 
if (v_strict_u2081_502_ == 0)
{
if (v_strict_u2082_503_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4));
v___x_523_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_522_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v_h_519_ = v_a_524_;
goto v___jp_518_;
}
else
{
lean_dec_ref(v_h_u2082_505_);
lean_dec_ref(v_h_u2081_504_);
lean_dec_ref(v_w_501_);
lean_dec_ref(v_v_500_);
lean_dec_ref(v_u_499_);
return v___x_523_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6));
v___x_526_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_525_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v_h_519_ = v_a_527_;
goto v___jp_518_;
}
else
{
lean_dec_ref(v_h_u2082_505_);
lean_dec_ref(v_h_u2081_504_);
lean_dec_ref(v_w_501_);
lean_dec_ref(v_v_500_);
lean_dec_ref(v_u_499_);
return v___x_526_;
}
}
}
else
{
if (v_strict_u2082_503_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8));
v___x_529_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_528_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v_h_519_ = v_a_530_;
goto v___jp_518_;
}
else
{
lean_dec_ref(v_h_u2082_505_);
lean_dec_ref(v_h_u2081_504_);
lean_dec_ref(v_w_501_);
lean_dec_ref(v_v_500_);
lean_dec_ref(v_u_499_);
return v___x_529_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10));
v___x_532_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_531_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v_h_519_ = v_a_533_;
goto v___jp_518_;
}
else
{
lean_dec_ref(v_h_u2082_505_);
lean_dec_ref(v_h_u2081_504_);
lean_dec_ref(v_w_501_);
lean_dec_ref(v_v_500_);
lean_dec_ref(v_u_499_);
return v___x_532_;
}
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = l_Lean_mkApp5(v_h_519_, v_u_499_, v_v_500_, v_w_501_, v_h_u2081_504_, v_h_u2082_505_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_499_ = stack[0].m_obj;
lean_object* v_v_500_ = stack[1].m_obj;
lean_object* v_w_501_ = stack[2].m_obj;
uint8_t v_strict_u2081_502_ = stack[3].m_num;
uint8_t v_strict_u2082_503_ = stack[4].m_num;
lean_object* v_h_u2081_504_ = stack[5].m_obj;
lean_object* v_h_u2082_505_ = stack[6].m_obj;
lean_object* v_a_506_ = stack[7].m_obj;
lean_object* v_a_507_ = stack[8].m_obj;
lean_object* v_a_508_ = stack[9].m_obj;
lean_object* v_a_509_ = stack[10].m_obj;
lean_object* v_a_510_ = stack[11].m_obj;
lean_object* v_a_511_ = stack[12].m_obj;
lean_object* v_a_512_ = stack[13].m_obj;
lean_object* v_a_513_ = stack[14].m_obj;
lean_object* v_a_514_ = stack[15].m_obj;
lean_object* v_a_515_ = stack[16].m_obj;
lean_object* v_a_516_ = stack[17].m_obj;
lean_object* v_res_534_;
v_res_534_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_499_, v_v_500_, v_w_501_, v_strict_u2081_502_, v_strict_u2082_503_, v_h_u2081_504_, v_h_u2082_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(lean_object** _args){
lean_object* v_u_535_ = _args[0];
lean_object* v_v_536_ = _args[1];
lean_object* v_w_537_ = _args[2];
lean_object* v_strict_u2081_538_ = _args[3];
lean_object* v_strict_u2082_539_ = _args[4];
lean_object* v_h_u2081_540_ = _args[5];
lean_object* v_h_u2082_541_ = _args[6];
lean_object* v_a_542_ = _args[7];
lean_object* v_a_543_ = _args[8];
lean_object* v_a_544_ = _args[9];
lean_object* v_a_545_ = _args[10];
lean_object* v_a_546_ = _args[11];
lean_object* v_a_547_ = _args[12];
lean_object* v_a_548_ = _args[13];
lean_object* v_a_549_ = _args[14];
lean_object* v_a_550_ = _args[15];
lean_object* v_a_551_ = _args[16];
lean_object* v_a_552_ = _args[17];
lean_object* v_a_553_ = _args[18];
_start:
{
uint8_t v_strict_u2081_boxed_554_; uint8_t v_strict_u2082_boxed_555_; lean_object* v_res_556_; 
v_strict_u2081_boxed_554_ = lean_unbox(v_strict_u2081_538_);
v_strict_u2082_boxed_555_ = lean_unbox(v_strict_u2082_539_);
v_res_556_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_535_, v_v_536_, v_w_537_, v_strict_u2081_boxed_554_, v_strict_u2082_boxed_555_, v_h_u2081_540_, v_h_u2082_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec(v_a_543_);
lean_dec(v_a_542_);
return v_res_556_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(lean_object* v_xs_557_, lean_object* v_i_558_){
_start:
{
lean_object* v_size_559_; uint8_t v___x_560_; 
v_size_559_ = lean_ctor_get(v_xs_557_, 2);
v___x_560_ = lean_nat_dec_lt(v_i_558_, v_size_559_);
return v___x_560_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_557_ = stack[0].m_obj;
lean_object* v_i_558_ = stack[1].m_obj;
uint8_t v_res_561_;
v_res_561_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_xs_557_, v_i_558_);
stack->m_num = v_res_561_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(lean_object* v_xs_562_, lean_object* v_i_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_xs_562_, v_i_563_);
lean_dec(v_i_563_);
lean_dec_ref(v_xs_562_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_nat_to_int(v___x_566_);
return v___x_567_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(lean_object* v_p_u2081_568_, lean_object* v_p_u2082_569_, lean_object* v_v_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_w_583_; lean_object* v_k_584_; lean_object* v_proof_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_644_; 
v_w_583_ = lean_ctor_get(v_p_u2081_568_, 0);
v_k_584_ = lean_ctor_get(v_p_u2081_568_, 1);
v_proof_585_ = lean_ctor_get(v_p_u2081_568_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_p_u2081_568_);
if (v_isSharedCheck_644_ == 0)
{
v___x_587_ = v_p_u2081_568_;
v_isShared_588_ = v_isSharedCheck_644_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_proof_585_);
lean_inc(v_k_584_);
lean_inc(v_w_583_);
lean_dec(v_p_u2081_568_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_644_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___y_590_; lean_object* v___y_591_; uint8_t v___y_592_; lean_object* v_k_598_; uint8_t v_strict_599_; lean_object* v_w_600_; lean_object* v_proof_601_; uint8_t v_strict_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_k_598_ = lean_ctor_get(v_p_u2082_569_, 1);
lean_inc_ref(v_k_598_);
v_strict_599_ = lean_ctor_get_uint8(v_k_584_, sizeof(void*)*1);
lean_dec_ref(v_k_584_);
v_w_600_ = lean_ctor_get(v_p_u2082_569_, 0);
lean_inc(v_w_600_);
v_proof_601_ = lean_ctor_get(v_p_u2082_569_, 2);
lean_inc_ref(v_proof_601_);
lean_dec_ref(v_p_u2082_569_);
v_strict_602_ = lean_ctor_get_uint8(v_k_598_, sizeof(void*)*1);
lean_dec_ref(v_k_598_);
v___x_603_ = l_Lean_instInhabitedExpr;
v___x_604_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_571_, v_a_572_, v_a_580_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v_nodes_621_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_629_; uint8_t v___x_633_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_nodes_621_ = lean_ctor_get(v_a_605_, 1);
lean_inc_ref(v_nodes_621_);
lean_dec(v_a_605_);
v___x_633_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_621_, v_w_583_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = l_outOfBounds___redArg(v___x_603_);
v___y_629_ = v___x_634_;
goto v___jp_628_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentArray_get_x21___redArg(v___x_603_, v_nodes_621_, v_w_583_);
v___y_629_ = v___x_635_;
goto v___jp_628_;
}
v___jp_606_:
{
lean_object* v___x_610_; 
v___x_610_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v___y_608_, v___y_607_, v___y_609_, v_strict_599_, v_strict_602_, v_proof_585_, v_proof_601_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
if (v_strict_599_ == 0)
{
v___y_590_ = v___x_612_;
v___y_591_ = v_a_611_;
v___y_592_ = v_strict_602_;
goto v___jp_589_;
}
else
{
v___y_590_ = v___x_612_;
v___y_591_ = v_a_611_;
v___y_592_ = v_strict_599_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_del_object(v___x_587_);
lean_dec(v_w_583_);
v_a_613_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_610_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
v___jp_622_:
{
uint8_t v___x_625_; 
v___x_625_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_621_, v_v_570_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v_nodes_621_);
v___x_626_ = l_outOfBounds___redArg(v___x_603_);
v___y_607_ = v___y_624_;
v___y_608_ = v___y_623_;
v___y_609_ = v___x_626_;
goto v___jp_606_;
}
else
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_PersistentArray_get_x21___redArg(v___x_603_, v_nodes_621_, v_v_570_);
lean_dec_ref(v_nodes_621_);
v___y_607_ = v___y_624_;
v___y_608_ = v___y_623_;
v___y_609_ = v___x_627_;
goto v___jp_606_;
}
}
v___jp_628_:
{
uint8_t v___x_630_; 
v___x_630_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_621_, v_w_600_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec(v_w_600_);
v___x_631_ = l_outOfBounds___redArg(v___x_603_);
v___y_623_ = v___y_629_;
v___y_624_ = v___x_631_;
goto v___jp_622_;
}
else
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentArray_get_x21___redArg(v___x_603_, v_nodes_621_, v_w_600_);
lean_dec(v_w_600_);
v___y_623_ = v___y_629_;
v___y_624_ = v___x_632_;
goto v___jp_622_;
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_proof_601_);
lean_dec(v_w_600_);
lean_del_object(v___x_587_);
lean_dec_ref(v_proof_585_);
lean_dec(v_w_583_);
v_a_636_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_604_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_604_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
v___jp_589_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc(v___y_590_);
v___x_593_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_593_, 0, v___y_590_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*1, v___y_592_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v___y_591_);
lean_ctor_set(v___x_587_, 1, v___x_593_);
v___x_595_ = v___x_587_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_w_583_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___y_591_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_568_ = stack[0].m_obj;
lean_object* v_p_u2082_569_ = stack[1].m_obj;
lean_object* v_v_570_ = stack[2].m_obj;
lean_object* v_a_571_ = stack[3].m_obj;
lean_object* v_a_572_ = stack[4].m_obj;
lean_object* v_a_573_ = stack[5].m_obj;
lean_object* v_a_574_ = stack[6].m_obj;
lean_object* v_a_575_ = stack[7].m_obj;
lean_object* v_a_576_ = stack[8].m_obj;
lean_object* v_a_577_ = stack[9].m_obj;
lean_object* v_a_578_ = stack[10].m_obj;
lean_object* v_a_579_ = stack[11].m_obj;
lean_object* v_a_580_ = stack[12].m_obj;
lean_object* v_a_581_ = stack[13].m_obj;
lean_object* v_res_645_;
v_res_645_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_568_, v_p_u2082_569_, v_v_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(lean_object* v_p_u2081_646_, lean_object* v_p_u2082_647_, lean_object* v_v_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_646_, v_p_u2082_647_, v_v_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec(v_a_649_);
lean_dec(v_v_648_);
return v_res_661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = l_Lean_Level_ofNat(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_box(0);
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4);
v___x_673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2));
v___x_674_ = l_Lean_Expr_const___override(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_box(0);
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7));
v___x_680_ = l_Lean_Expr_const___override(v___x_679_, v___x_678_);
return v___x_680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_box(0);
v___x_686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10));
v___x_687_ = l_Lean_Expr_const___override(v___x_686_, v___x_685_);
return v___x_687_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(lean_object* v_u_712_, lean_object* v_v_713_, lean_object* v_w_714_, lean_object* v_k_u2081_715_, lean_object* v_k_u2082_716_, lean_object* v_h_u2081_717_, lean_object* v_h_u2082_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v_k_772_; uint8_t v_strict_773_; lean_object* v_h_775_; 
v_k_772_ = lean_ctor_get(v_k_u2081_715_, 0);
v_strict_773_ = lean_ctor_get_uint8(v_k_u2081_715_, sizeof(void*)*1);
if (v_strict_773_ == 0)
{
uint8_t v_strict_789_; 
v_strict_789_ = lean_ctor_get_uint8(v_k_u2082_716_, sizeof(void*)*1);
if (v_strict_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13));
v___x_791_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_790_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_h_775_ = v_a_792_;
goto v___jp_774_;
}
else
{
lean_dec_ref(v_h_u2082_718_);
lean_dec_ref(v_h_u2081_717_);
lean_dec_ref(v_w_714_);
lean_dec_ref(v_v_713_);
lean_dec_ref(v_u_712_);
return v___x_791_;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15));
v___x_794_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_793_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v_h_775_ = v_a_795_;
goto v___jp_774_;
}
else
{
lean_dec_ref(v_h_u2082_718_);
lean_dec_ref(v_h_u2081_717_);
lean_dec_ref(v_w_714_);
lean_dec_ref(v_v_713_);
lean_dec_ref(v_u_712_);
return v___x_794_;
}
}
}
else
{
uint8_t v_strict_796_; 
v_strict_796_ = lean_ctor_get_uint8(v_k_u2082_716_, sizeof(void*)*1);
if (v_strict_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17));
v___x_798_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_797_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v_h_775_ = v_a_799_;
goto v___jp_774_;
}
else
{
lean_dec_ref(v_h_u2082_718_);
lean_dec_ref(v_h_u2081_717_);
lean_dec_ref(v_w_714_);
lean_dec_ref(v_v_713_);
lean_dec_ref(v_u_712_);
return v___x_798_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19));
v___x_801_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_800_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v_h_775_ = v_a_802_;
goto v___jp_774_;
}
else
{
lean_dec_ref(v_h_u2082_718_);
lean_dec_ref(v_h_u2081_717_);
lean_dec_ref(v_w_714_);
lean_dec_ref(v_v_713_);
lean_dec_ref(v_u_712_);
return v___x_801_;
}
}
}
v___jp_731_:
{
lean_object* v_h_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_h_736_ = l_Lean_mkApp6(v___y_732_, v_u_712_, v_v_713_, v_w_714_, v___y_734_, v___y_733_, v___y_735_);
v___x_737_ = l_Lean_eagerReflBoolTrue;
v___x_738_ = l_Lean_mkApp3(v_h_736_, v_h_u2081_717_, v_h_u2082_718_, v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
v___jp_740_:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_746_ = lean_int_dec_le(v___x_745_, v___y_743_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_750_ = lean_int_neg(v___y_743_);
lean_dec(v___y_743_);
v___x_751_ = l_Int_toNat(v___x_750_);
lean_dec(v___x_750_);
v___x_752_ = l_Lean_instToExprInt_mkNat(v___x_751_);
v___x_753_ = l_Lean_mkApp3(v___x_747_, v___x_748_, v___x_749_, v___x_752_);
v___y_732_ = v___y_741_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_742_;
v___y_735_ = v___x_753_;
goto v___jp_731_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l_Int_toNat(v___y_743_);
lean_dec(v___y_743_);
v___x_755_ = l_Lean_instToExprInt_mkNat(v___x_754_);
v___y_732_ = v___y_741_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_742_;
v___y_735_ = v___x_755_;
goto v___jp_731_;
}
}
v___jp_756_:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_762_ = lean_int_dec_le(v___x_761_, v___y_758_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_766_ = lean_int_neg(v___y_758_);
v___x_767_ = l_Int_toNat(v___x_766_);
lean_dec(v___x_766_);
v___x_768_ = l_Lean_instToExprInt_mkNat(v___x_767_);
v___x_769_ = l_Lean_mkApp3(v___x_763_, v___x_764_, v___x_765_, v___x_768_);
v___y_741_ = v___y_757_;
v___y_742_ = v___y_760_;
v___y_743_ = v___y_759_;
v___y_744_ = v___x_769_;
goto v___jp_740_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = l_Int_toNat(v___y_758_);
v___x_771_ = l_Lean_instToExprInt_mkNat(v___x_770_);
v___y_741_ = v___y_757_;
v___y_742_ = v___y_760_;
v___y_743_ = v___y_759_;
v___y_744_ = v___x_771_;
goto v___jp_740_;
}
}
v___jp_774_:
{
lean_object* v_k_776_; lean_object* v_k_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_k_776_ = lean_ctor_get(v_k_u2082_716_, 0);
v_k_777_ = lean_int_add(v_k_772_, v_k_776_);
v___x_778_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_779_ = lean_int_dec_le(v___x_778_, v_k_772_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_783_ = lean_int_neg(v_k_772_);
v___x_784_ = l_Int_toNat(v___x_783_);
lean_dec(v___x_783_);
v___x_785_ = l_Lean_instToExprInt_mkNat(v___x_784_);
v___x_786_ = l_Lean_mkApp3(v___x_780_, v___x_781_, v___x_782_, v___x_785_);
v___y_757_ = v_h_775_;
v___y_758_ = v_k_776_;
v___y_759_ = v_k_777_;
v___y_760_ = v___x_786_;
goto v___jp_756_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = l_Int_toNat(v_k_772_);
v___x_788_ = l_Lean_instToExprInt_mkNat(v___x_787_);
v___y_757_ = v_h_775_;
v___y_758_ = v_k_776_;
v___y_759_ = v_k_777_;
v___y_760_ = v___x_788_;
goto v___jp_756_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_712_ = stack[0].m_obj;
lean_object* v_v_713_ = stack[1].m_obj;
lean_object* v_w_714_ = stack[2].m_obj;
lean_object* v_k_u2081_715_ = stack[3].m_obj;
lean_object* v_k_u2082_716_ = stack[4].m_obj;
lean_object* v_h_u2081_717_ = stack[5].m_obj;
lean_object* v_h_u2082_718_ = stack[6].m_obj;
lean_object* v_a_719_ = stack[7].m_obj;
lean_object* v_a_720_ = stack[8].m_obj;
lean_object* v_a_721_ = stack[9].m_obj;
lean_object* v_a_722_ = stack[10].m_obj;
lean_object* v_a_723_ = stack[11].m_obj;
lean_object* v_a_724_ = stack[12].m_obj;
lean_object* v_a_725_ = stack[13].m_obj;
lean_object* v_a_726_ = stack[14].m_obj;
lean_object* v_a_727_ = stack[15].m_obj;
lean_object* v_a_728_ = stack[16].m_obj;
lean_object* v_a_729_ = stack[17].m_obj;
lean_object* v_res_803_;
v_res_803_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_712_, v_v_713_, v_w_714_, v_k_u2081_715_, v_k_u2082_716_, v_h_u2081_717_, v_h_u2082_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
stack->m_obj
 = v_res_803_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(lean_object** _args){
lean_object* v_u_804_ = _args[0];
lean_object* v_v_805_ = _args[1];
lean_object* v_w_806_ = _args[2];
lean_object* v_k_u2081_807_ = _args[3];
lean_object* v_k_u2082_808_ = _args[4];
lean_object* v_h_u2081_809_ = _args[5];
lean_object* v_h_u2082_810_ = _args[6];
lean_object* v_a_811_ = _args[7];
lean_object* v_a_812_ = _args[8];
lean_object* v_a_813_ = _args[9];
lean_object* v_a_814_ = _args[10];
lean_object* v_a_815_ = _args[11];
lean_object* v_a_816_ = _args[12];
lean_object* v_a_817_ = _args[13];
lean_object* v_a_818_ = _args[14];
lean_object* v_a_819_ = _args[15];
lean_object* v_a_820_ = _args[16];
lean_object* v_a_821_ = _args[17];
lean_object* v_a_822_ = _args[18];
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_804_, v_v_805_, v_w_806_, v_k_u2081_807_, v_k_u2082_808_, v_h_u2081_809_, v_h_u2082_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_k_u2082_808_);
lean_dec_ref(v_k_u2081_807_);
return v_res_823_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(lean_object* v_p_u2081_824_, lean_object* v_p_u2082_825_, lean_object* v_v_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_w_839_; lean_object* v_k_840_; lean_object* v_proof_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_902_; 
v_w_839_ = lean_ctor_get(v_p_u2081_824_, 0);
v_k_840_ = lean_ctor_get(v_p_u2081_824_, 1);
v_proof_841_ = lean_ctor_get(v_p_u2081_824_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_p_u2081_824_);
if (v_isSharedCheck_902_ == 0)
{
v___x_843_ = v_p_u2081_824_;
v_isShared_844_ = v_isSharedCheck_902_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_proof_841_);
lean_inc(v_k_840_);
lean_inc(v_w_839_);
lean_dec(v_p_u2081_824_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_902_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_848_; lean_object* v_w_854_; lean_object* v_k_855_; lean_object* v_proof_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_w_854_ = lean_ctor_get(v_p_u2082_825_, 0);
lean_inc(v_w_854_);
v_k_855_ = lean_ctor_get(v_p_u2082_825_, 1);
lean_inc_ref(v_k_855_);
v_proof_856_ = lean_ctor_get(v_p_u2082_825_, 2);
lean_inc_ref(v_proof_856_);
lean_dec_ref(v_p_u2082_825_);
v___x_857_ = l_Lean_instInhabitedExpr;
v___x_858_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_827_, v_a_828_, v_a_836_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v_nodes_879_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_887_; uint8_t v___x_891_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v_nodes_879_ = lean_ctor_get(v_a_859_, 1);
lean_inc_ref(v_nodes_879_);
lean_dec(v_a_859_);
v___x_891_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_879_, v_w_839_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
v___x_892_ = l_outOfBounds___redArg(v___x_857_);
v___y_887_ = v___x_892_;
goto v___jp_886_;
}
else
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentArray_get_x21___redArg(v___x_857_, v_nodes_879_, v_w_839_);
v___y_887_ = v___x_893_;
goto v___jp_886_;
}
v___jp_860_:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v___y_862_, v___y_861_, v___y_863_, v_k_840_, v_k_855_, v_proof_841_, v_proof_856_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_k_866_; uint8_t v_strict_867_; lean_object* v_k_868_; uint8_t v_strict_869_; lean_object* v___x_870_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v_k_866_ = lean_ctor_get(v_k_840_, 0);
lean_inc(v_k_866_);
v_strict_867_ = lean_ctor_get_uint8(v_k_840_, sizeof(void*)*1);
lean_dec_ref(v_k_840_);
v_k_868_ = lean_ctor_get(v_k_855_, 0);
lean_inc(v_k_868_);
v_strict_869_ = lean_ctor_get_uint8(v_k_855_, sizeof(void*)*1);
lean_dec_ref(v_k_855_);
v___x_870_ = lean_int_add(v_k_866_, v_k_868_);
lean_dec(v_k_868_);
lean_dec(v_k_866_);
if (v_strict_867_ == 0)
{
v___y_846_ = v___x_870_;
v___y_847_ = v_a_865_;
v___y_848_ = v_strict_869_;
goto v___jp_845_;
}
else
{
v___y_846_ = v___x_870_;
v___y_847_ = v_a_865_;
v___y_848_ = v_strict_867_;
goto v___jp_845_;
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v_k_855_);
lean_del_object(v___x_843_);
lean_dec_ref(v_k_840_);
lean_dec(v_w_839_);
v_a_871_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_864_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_864_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
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
v___jp_880_:
{
uint8_t v___x_883_; 
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_879_, v_v_826_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v_nodes_879_);
v___x_884_ = l_outOfBounds___redArg(v___x_857_);
v___y_861_ = v___y_882_;
v___y_862_ = v___y_881_;
v___y_863_ = v___x_884_;
goto v___jp_860_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentArray_get_x21___redArg(v___x_857_, v_nodes_879_, v_v_826_);
lean_dec_ref(v_nodes_879_);
v___y_861_ = v___y_882_;
v___y_862_ = v___y_881_;
v___y_863_ = v___x_885_;
goto v___jp_860_;
}
}
v___jp_886_:
{
uint8_t v___x_888_; 
v___x_888_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_879_, v_w_854_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v_w_854_);
v___x_889_ = l_outOfBounds___redArg(v___x_857_);
v___y_881_ = v___y_887_;
v___y_882_ = v___x_889_;
goto v___jp_880_;
}
else
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_PersistentArray_get_x21___redArg(v___x_857_, v_nodes_879_, v_w_854_);
lean_dec(v_w_854_);
v___y_881_ = v___y_887_;
v___y_882_ = v___x_890_;
goto v___jp_880_;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_proof_856_);
lean_dec_ref(v_k_855_);
lean_dec(v_w_854_);
lean_del_object(v___x_843_);
lean_dec_ref(v_proof_841_);
lean_dec_ref(v_k_840_);
lean_dec(v_w_839_);
v_a_894_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_858_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_858_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
v___jp_845_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_849_, 0, v___y_846_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___y_848_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 2, v___y_847_);
lean_ctor_set(v___x_843_, 1, v___x_849_);
v___x_851_ = v___x_843_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_w_839_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v___y_847_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_824_ = stack[0].m_obj;
lean_object* v_p_u2082_825_ = stack[1].m_obj;
lean_object* v_v_826_ = stack[2].m_obj;
lean_object* v_a_827_ = stack[3].m_obj;
lean_object* v_a_828_ = stack[4].m_obj;
lean_object* v_a_829_ = stack[5].m_obj;
lean_object* v_a_830_ = stack[6].m_obj;
lean_object* v_a_831_ = stack[7].m_obj;
lean_object* v_a_832_ = stack[8].m_obj;
lean_object* v_a_833_ = stack[9].m_obj;
lean_object* v_a_834_ = stack[10].m_obj;
lean_object* v_a_835_ = stack[11].m_obj;
lean_object* v_a_836_ = stack[12].m_obj;
lean_object* v_a_837_ = stack[13].m_obj;
lean_object* v_res_903_;
v_res_903_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_824_, v_p_u2082_825_, v_v_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(lean_object* v_p_u2081_904_, lean_object* v_p_u2082_905_, lean_object* v_v_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_904_, v_p_u2082_905_, v_v_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_v_906_);
return v_res_919_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object* v_p_u2081_920_, lean_object* v_p_u2082_921_, lean_object* v_v_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_Grind_Order_isRing(v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; uint8_t v___x_937_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = lean_unbox(v_a_936_);
lean_dec(v_a_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_920_, v_p_u2082_921_, v_v_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_920_, v_p_u2082_921_, v_v_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
return v___x_939_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_p_u2082_921_);
lean_dec_ref(v_p_u2081_920_);
v_a_940_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_935_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_935_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkTrans_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_920_ = stack[0].m_obj;
lean_object* v_p_u2082_921_ = stack[1].m_obj;
lean_object* v_v_922_ = stack[2].m_obj;
lean_object* v_a_923_ = stack[3].m_obj;
lean_object* v_a_924_ = stack[4].m_obj;
lean_object* v_a_925_ = stack[5].m_obj;
lean_object* v_a_926_ = stack[6].m_obj;
lean_object* v_a_927_ = stack[7].m_obj;
lean_object* v_a_928_ = stack[8].m_obj;
lean_object* v_a_929_ = stack[9].m_obj;
lean_object* v_a_930_ = stack[10].m_obj;
lean_object* v_a_931_ = stack[11].m_obj;
lean_object* v_a_932_ = stack[12].m_obj;
lean_object* v_a_933_ = stack[13].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Meta_Grind_Order_mkTrans(v_p_u2081_920_, v_p_u2082_921_, v_v_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans___boxed(lean_object* v_p_u2081_949_, lean_object* v_p_u2082_950_, lean_object* v_v_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Meta_Grind_Order_mkTrans(v_p_u2081_949_, v_p_u2082_950_, v_v_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
lean_dec(v_v_951_);
return v_res_964_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_965_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_1542__overap_981_; lean_object* v___x_982_; 
v___x_979_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0);
v___f_980_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_980_, 0, v___x_979_);
v___x_1542__overap_981_ = lean_panic_fn_borrowed(v___f_980_, v_msg_966_);
lean_dec_ref(v___f_980_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc(v___y_968_);
lean_inc(v___y_967_);
v___x_982_ = lean_apply_12(v___x_1542__overap_981_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, lean_box(0));
return v___x_982_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_966_ = stack[0].m_obj;
lean_object* v___y_967_ = stack[1].m_obj;
lean_object* v___y_968_ = stack[2].m_obj;
lean_object* v___y_969_ = stack[3].m_obj;
lean_object* v___y_970_ = stack[4].m_obj;
lean_object* v___y_971_ = stack[5].m_obj;
lean_object* v___y_972_ = stack[6].m_obj;
lean_object* v___y_973_ = stack[7].m_obj;
lean_object* v___y_974_ = stack[8].m_obj;
lean_object* v___y_975_ = stack[9].m_obj;
lean_object* v___y_976_ = stack[10].m_obj;
lean_object* v___y_977_ = stack[11].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v_msg_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec(v___y_986_);
lean_dec(v___y_985_);
return v_res_997_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2));
v___x_1002_ = lean_unsigned_to_nat(4u);
v___x_1003_ = lean_unsigned_to_nat(133u);
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1));
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1006_ = l_mkPanicMessageWithDecl(v___x_1005_, v___x_1004_, v___x_1003_, v___x_1002_, v___x_1001_);
return v___x_1006_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(lean_object* v_u_1013_, lean_object* v_v_1014_, lean_object* v_k_1015_, lean_object* v_huv_1016_, lean_object* v_k_x27_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
uint8_t v_strict_1033_; uint8_t v_strict_1034_; 
v_strict_1033_ = lean_ctor_get_uint8(v_k_1015_, sizeof(void*)*1);
v_strict_1034_ = lean_ctor_get_uint8(v_k_x27_1017_, sizeof(void*)*1);
if (v_strict_1034_ == 0)
{
if (v_strict_1033_ == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_v_1014_);
lean_dec_ref(v_u_1013_);
v___x_1047_ = l_Lean_Meta_mkEqTrue(v_huv_1016_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1047_;
}
else
{
goto v___jp_1035_;
}
}
else
{
if (v_strict_1033_ == 0)
{
goto v___jp_1035_;
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref(v_v_1014_);
lean_dec_ref(v_u_1013_);
v___x_1048_ = l_Lean_Meta_mkEqTrue(v_huv_1016_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1048_;
}
}
v___jp_1030_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3);
v___x_1032_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1031_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1032_;
}
v___jp_1035_:
{
if (v_strict_1033_ == 0)
{
lean_dec_ref(v_huv_1016_);
lean_dec_ref(v_v_1014_);
lean_dec_ref(v_u_1013_);
goto v___jp_1030_;
}
else
{
if (v_strict_1034_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5));
v___x_1037_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_1036_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = l_Lean_mkApp3(v_a_1038_, v_u_1013_, v_v_1014_, v_huv_1016_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_dec_ref(v_huv_1016_);
lean_dec_ref(v_v_1014_);
lean_dec_ref(v_u_1013_);
return v___x_1037_;
}
}
else
{
lean_dec_ref(v_huv_1016_);
lean_dec_ref(v_v_1014_);
lean_dec_ref(v_u_1013_);
goto v___jp_1030_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1013_ = stack[0].m_obj;
lean_object* v_v_1014_ = stack[1].m_obj;
lean_object* v_k_1015_ = stack[2].m_obj;
lean_object* v_huv_1016_ = stack[3].m_obj;
lean_object* v_k_x27_1017_ = stack[4].m_obj;
lean_object* v_a_1018_ = stack[5].m_obj;
lean_object* v_a_1019_ = stack[6].m_obj;
lean_object* v_a_1020_ = stack[7].m_obj;
lean_object* v_a_1021_ = stack[8].m_obj;
lean_object* v_a_1022_ = stack[9].m_obj;
lean_object* v_a_1023_ = stack[10].m_obj;
lean_object* v_a_1024_ = stack[11].m_obj;
lean_object* v_a_1025_ = stack[12].m_obj;
lean_object* v_a_1026_ = stack[13].m_obj;
lean_object* v_a_1027_ = stack[14].m_obj;
lean_object* v_a_1028_ = stack[15].m_obj;
lean_object* v_res_1049_;
v_res_1049_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1013_, v_v_1014_, v_k_1015_, v_huv_1016_, v_k_x27_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___boxed(lean_object** _args){
lean_object* v_u_1050_ = _args[0];
lean_object* v_v_1051_ = _args[1];
lean_object* v_k_1052_ = _args[2];
lean_object* v_huv_1053_ = _args[3];
lean_object* v_k_x27_1054_ = _args[4];
lean_object* v_a_1055_ = _args[5];
lean_object* v_a_1056_ = _args[6];
lean_object* v_a_1057_ = _args[7];
lean_object* v_a_1058_ = _args[8];
lean_object* v_a_1059_ = _args[9];
lean_object* v_a_1060_ = _args[10];
lean_object* v_a_1061_ = _args[11];
lean_object* v_a_1062_ = _args[12];
lean_object* v_a_1063_ = _args[13];
lean_object* v_a_1064_ = _args[14];
lean_object* v_a_1065_ = _args[15];
lean_object* v_a_1066_ = _args[16];
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1050_, v_v_1051_, v_k_1052_, v_huv_1053_, v_k_x27_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_k_x27_1054_);
lean_dec_ref(v_k_1052_);
return v_res_1067_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(lean_object* v_u_1092_, lean_object* v_v_1093_, lean_object* v_k_1094_, lean_object* v_huv_1095_, lean_object* v_k_x27_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v_k_1116_; uint8_t v_strict_1117_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1133_; 
v_k_1116_ = lean_ctor_get(v_k_x27_1096_, 0);
v_strict_1117_ = lean_ctor_get_uint8(v_k_x27_1096_, sizeof(void*)*1);
if (v_strict_1117_ == 0)
{
uint8_t v_strict_1148_; 
v_strict_1148_ = lean_ctor_get_uint8(v_k_1094_, sizeof(void*)*1);
if (v_strict_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1));
v___y_1133_ = v___x_1149_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3));
v___y_1133_ = v___x_1150_;
goto v___jp_1132_;
}
}
else
{
uint8_t v_strict_1151_; 
v_strict_1151_ = lean_ctor_get_uint8(v_k_1094_, sizeof(void*)*1);
if (v_strict_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5));
v___y_1133_ = v___x_1152_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7));
v___y_1133_ = v___x_1153_;
goto v___jp_1132_;
}
}
v___jp_1109_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = l_Lean_eagerReflBoolTrue;
v___x_1114_ = l_Lean_mkApp6(v___y_1111_, v_u_1092_, v_v_1093_, v___y_1110_, v___y_1112_, v___x_1113_, v_huv_1095_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
v___jp_1118_:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1122_ = lean_int_dec_le(v___x_1121_, v_k_1116_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1126_ = lean_int_neg(v_k_1116_);
v___x_1127_ = l_Int_toNat(v___x_1126_);
lean_dec(v___x_1126_);
v___x_1128_ = l_Lean_instToExprInt_mkNat(v___x_1127_);
v___x_1129_ = l_Lean_mkApp3(v___x_1123_, v___x_1124_, v___x_1125_, v___x_1128_);
v___y_1110_ = v___y_1120_;
v___y_1111_ = v___y_1119_;
v___y_1112_ = v___x_1129_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = l_Int_toNat(v_k_1116_);
v___x_1131_ = l_Lean_instToExprInt_mkNat(v___x_1130_);
v___y_1110_ = v___y_1120_;
v___y_1111_ = v___y_1119_;
v___y_1112_ = v___x_1131_;
goto v___jp_1109_;
}
}
v___jp_1132_:
{
lean_object* v___x_1134_; 
lean_inc(v___y_1133_);
v___x_1134_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1133_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_k_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v_k_1136_ = lean_ctor_get(v_k_1094_, 0);
v___x_1137_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1138_ = lean_int_dec_le(v___x_1137_, v_k_1136_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1142_ = lean_int_neg(v_k_1136_);
v___x_1143_ = l_Int_toNat(v___x_1142_);
lean_dec(v___x_1142_);
v___x_1144_ = l_Lean_instToExprInt_mkNat(v___x_1143_);
v___x_1145_ = l_Lean_mkApp3(v___x_1139_, v___x_1140_, v___x_1141_, v___x_1144_);
v___y_1119_ = v_a_1135_;
v___y_1120_ = v___x_1145_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l_Int_toNat(v_k_1136_);
v___x_1147_ = l_Lean_instToExprInt_mkNat(v___x_1146_);
v___y_1119_ = v_a_1135_;
v___y_1120_ = v___x_1147_;
goto v___jp_1118_;
}
}
else
{
lean_dec_ref(v_huv_1095_);
lean_dec_ref(v_v_1093_);
lean_dec_ref(v_u_1092_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1092_ = stack[0].m_obj;
lean_object* v_v_1093_ = stack[1].m_obj;
lean_object* v_k_1094_ = stack[2].m_obj;
lean_object* v_huv_1095_ = stack[3].m_obj;
lean_object* v_k_x27_1096_ = stack[4].m_obj;
lean_object* v_a_1097_ = stack[5].m_obj;
lean_object* v_a_1098_ = stack[6].m_obj;
lean_object* v_a_1099_ = stack[7].m_obj;
lean_object* v_a_1100_ = stack[8].m_obj;
lean_object* v_a_1101_ = stack[9].m_obj;
lean_object* v_a_1102_ = stack[10].m_obj;
lean_object* v_a_1103_ = stack[11].m_obj;
lean_object* v_a_1104_ = stack[12].m_obj;
lean_object* v_a_1105_ = stack[13].m_obj;
lean_object* v_a_1106_ = stack[14].m_obj;
lean_object* v_a_1107_ = stack[15].m_obj;
lean_object* v_res_1154_;
v_res_1154_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1092_, v_v_1093_, v_k_1094_, v_huv_1095_, v_k_x27_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
stack->m_obj
 = v_res_1154_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(lean_object** _args){
lean_object* v_u_1155_ = _args[0];
lean_object* v_v_1156_ = _args[1];
lean_object* v_k_1157_ = _args[2];
lean_object* v_huv_1158_ = _args[3];
lean_object* v_k_x27_1159_ = _args[4];
lean_object* v_a_1160_ = _args[5];
lean_object* v_a_1161_ = _args[6];
lean_object* v_a_1162_ = _args[7];
lean_object* v_a_1163_ = _args[8];
lean_object* v_a_1164_ = _args[9];
lean_object* v_a_1165_ = _args[10];
lean_object* v_a_1166_ = _args[11];
lean_object* v_a_1167_ = _args[12];
lean_object* v_a_1168_ = _args[13];
lean_object* v_a_1169_ = _args[14];
lean_object* v_a_1170_ = _args[15];
lean_object* v_a_1171_ = _args[16];
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1155_, v_v_1156_, v_k_1157_, v_huv_1158_, v_k_x27_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
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
lean_dec(v_a_1160_);
lean_dec_ref(v_k_x27_1159_);
lean_dec_ref(v_k_1157_);
return v_res_1172_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object* v_u_1173_, lean_object* v_v_1174_, lean_object* v_k_1175_, lean_object* v_huv_1176_, lean_object* v_k_x27_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_Grind_Order_isRing(v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; uint8_t v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = lean_unbox(v_a_1191_);
lean_dec(v_a_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1173_, v_v_1174_, v_k_1175_, v_huv_1176_, v_k_x27_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1173_, v_v_1174_, v_k_1175_, v_huv_1176_, v_k_x27_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1194_;
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_huv_1176_);
lean_dec_ref(v_v_1174_);
lean_dec_ref(v_u_1173_);
v_a_1195_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1190_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1190_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1173_ = stack[0].m_obj;
lean_object* v_v_1174_ = stack[1].m_obj;
lean_object* v_k_1175_ = stack[2].m_obj;
lean_object* v_huv_1176_ = stack[3].m_obj;
lean_object* v_k_x27_1177_ = stack[4].m_obj;
lean_object* v_a_1178_ = stack[5].m_obj;
lean_object* v_a_1179_ = stack[6].m_obj;
lean_object* v_a_1180_ = stack[7].m_obj;
lean_object* v_a_1181_ = stack[8].m_obj;
lean_object* v_a_1182_ = stack[9].m_obj;
lean_object* v_a_1183_ = stack[10].m_obj;
lean_object* v_a_1184_ = stack[11].m_obj;
lean_object* v_a_1185_ = stack[12].m_obj;
lean_object* v_a_1186_ = stack[13].m_obj;
lean_object* v_a_1187_ = stack[14].m_obj;
lean_object* v_a_1188_ = stack[15].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_u_1173_, v_v_1174_, v_k_1175_, v_huv_1176_, v_k_x27_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof___boxed(lean_object** _args){
lean_object* v_u_1204_ = _args[0];
lean_object* v_v_1205_ = _args[1];
lean_object* v_k_1206_ = _args[2];
lean_object* v_huv_1207_ = _args[3];
lean_object* v_k_x27_1208_ = _args[4];
lean_object* v_a_1209_ = _args[5];
lean_object* v_a_1210_ = _args[6];
lean_object* v_a_1211_ = _args[7];
lean_object* v_a_1212_ = _args[8];
lean_object* v_a_1213_ = _args[9];
lean_object* v_a_1214_ = _args[10];
lean_object* v_a_1215_ = _args[11];
lean_object* v_a_1216_ = _args[12];
lean_object* v_a_1217_ = _args[13];
lean_object* v_a_1218_ = _args[14];
lean_object* v_a_1219_ = _args[15];
lean_object* v_a_1220_ = _args[16];
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_u_1204_, v_v_1205_, v_k_1206_, v_huv_1207_, v_k_x27_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_k_x27_1208_);
lean_dec_ref(v_k_1206_);
return v_res_1221_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(lean_object* v_u_1234_, lean_object* v_k_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v_k_1254_; uint8_t v_strict_1255_; lean_object* v___y_1257_; 
v_k_1254_ = lean_ctor_get(v_k_1235_, 0);
v_strict_1255_ = lean_ctor_get_uint8(v_k_1235_, sizeof(void*)*1);
if (v_strict_1255_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1));
v___y_1257_ = v___x_1271_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1272_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3));
v___y_1257_ = v___x_1272_;
goto v___jp_1256_;
}
v___jp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = l_Lean_eagerReflBoolTrue;
v___x_1252_ = l_Lean_mkApp3(v___y_1249_, v_u_1234_, v___y_1250_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; 
lean_inc(v___y_1257_);
v___x_1258_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1257_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1261_ = lean_int_dec_le(v___x_1260_, v_k_1254_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1265_ = lean_int_neg(v_k_1254_);
v___x_1266_ = l_Int_toNat(v___x_1265_);
lean_dec(v___x_1265_);
v___x_1267_ = l_Lean_instToExprInt_mkNat(v___x_1266_);
v___x_1268_ = l_Lean_mkApp3(v___x_1262_, v___x_1263_, v___x_1264_, v___x_1267_);
v___y_1249_ = v_a_1259_;
v___y_1250_ = v___x_1268_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Int_toNat(v_k_1254_);
v___x_1270_ = l_Lean_instToExprInt_mkNat(v___x_1269_);
v___y_1249_ = v_a_1259_;
v___y_1250_ = v___x_1270_;
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v_u_1234_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1234_ = stack[0].m_obj;
lean_object* v_k_1235_ = stack[1].m_obj;
lean_object* v_a_1236_ = stack[2].m_obj;
lean_object* v_a_1237_ = stack[3].m_obj;
lean_object* v_a_1238_ = stack[4].m_obj;
lean_object* v_a_1239_ = stack[5].m_obj;
lean_object* v_a_1240_ = stack[6].m_obj;
lean_object* v_a_1241_ = stack[7].m_obj;
lean_object* v_a_1242_ = stack[8].m_obj;
lean_object* v_a_1243_ = stack[9].m_obj;
lean_object* v_a_1244_ = stack[10].m_obj;
lean_object* v_a_1245_ = stack[11].m_obj;
lean_object* v_a_1246_ = stack[12].m_obj;
lean_object* v_res_1273_;
v_res_1273_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1234_, v_k_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
stack->m_obj
 = v_res_1273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(lean_object* v_u_1274_, lean_object* v_k_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1274_, v_k_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_k_1275_);
return v_res_1288_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(lean_object* v_u_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1));
v___x_1309_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_1308_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_Lean_Expr_app___override(v_a_1310_, v_u_1295_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_dec_ref(v_u_1295_);
return v___x_1309_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1295_ = stack[0].m_obj;
lean_object* v_a_1296_ = stack[1].m_obj;
lean_object* v_a_1297_ = stack[2].m_obj;
lean_object* v_a_1298_ = stack[3].m_obj;
lean_object* v_a_1299_ = stack[4].m_obj;
lean_object* v_a_1300_ = stack[5].m_obj;
lean_object* v_a_1301_ = stack[6].m_obj;
lean_object* v_a_1302_ = stack[7].m_obj;
lean_object* v_a_1303_ = stack[8].m_obj;
lean_object* v_a_1304_ = stack[9].m_obj;
lean_object* v_a_1305_ = stack[10].m_obj;
lean_object* v_a_1306_ = stack[11].m_obj;
lean_object* v_res_1319_;
v_res_1319_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
stack->m_obj
 = v_res_1319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___boxed(lean_object* v_u_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec(v_a_1321_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1));
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = lean_unsigned_to_nat(175u);
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0));
v___x_1340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1341_ = l_mkPanicMessageWithDecl(v___x_1340_, v___x_1339_, v___x_1338_, v___x_1337_, v___x_1336_);
return v___x_1341_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object* v_u_1342_, lean_object* v_k_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Meta_Grind_Order_isRing(v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; uint8_t v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_unbox(v_a_1357_);
lean_dec(v_a_1357_);
if (v___x_1358_ == 0)
{
uint8_t v_strict_1359_; 
v_strict_1359_ = lean_ctor_get_uint8(v_k_1343_, sizeof(void*)*1);
if (v_strict_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1342_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec_ref(v_u_1342_);
v___x_1361_ = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2);
v___x_1362_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1361_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1362_;
}
}
else
{
lean_object* v___x_1363_; 
v___x_1363_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1342_, v_k_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1363_;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_u_1342_);
v_a_1364_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1356_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1356_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1342_ = stack[0].m_obj;
lean_object* v_k_1343_ = stack[1].m_obj;
lean_object* v_a_1344_ = stack[2].m_obj;
lean_object* v_a_1345_ = stack[3].m_obj;
lean_object* v_a_1346_ = stack[4].m_obj;
lean_object* v_a_1347_ = stack[5].m_obj;
lean_object* v_a_1348_ = stack[6].m_obj;
lean_object* v_a_1349_ = stack[7].m_obj;
lean_object* v_a_1350_ = stack[8].m_obj;
lean_object* v_a_1351_ = stack[9].m_obj;
lean_object* v_a_1352_ = stack[10].m_obj;
lean_object* v_a_1353_ = stack[11].m_obj;
lean_object* v_a_1354_ = stack[12].m_obj;
lean_object* v_res_1372_;
v_res_1372_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_u_1342_, v_k_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
stack->m_obj
 = v_res_1372_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___boxed(lean_object* v_u_1373_, lean_object* v_k_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_u_1373_, v_k_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_k_1374_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(lean_object* v_msg_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_panic_fn_borrowed(v___x_1389_, v_msg_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1));
v___x_1394_ = lean_unsigned_to_nat(22u);
v___x_1395_ = lean_unsigned_to_nat(183u);
v___x_1396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0));
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1398_ = l_mkPanicMessageWithDecl(v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_, v___x_1393_);
return v___x_1398_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(lean_object* v_u_1417_, lean_object* v_v_1418_, lean_object* v_k_1419_, lean_object* v_huv_1420_, lean_object* v_k_x27_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___y_1435_; uint8_t v_strict_1446_; 
v_strict_1446_ = lean_ctor_get_uint8(v_k_x27_1421_, sizeof(void*)*1);
if (v_strict_1446_ == 0)
{
uint8_t v_strict_1447_; 
v_strict_1447_ = lean_ctor_get_uint8(v_k_1419_, sizeof(void*)*1);
if (v_strict_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2);
v___x_1449_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_1448_);
v___y_1435_ = v___x_1449_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4));
v___y_1435_ = v___x_1450_;
goto v___jp_1434_;
}
}
else
{
uint8_t v_strict_1451_; 
v_strict_1451_ = lean_ctor_get_uint8(v_k_1419_, sizeof(void*)*1);
if (v_strict_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6));
v___y_1435_ = v___x_1452_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8));
v___y_1435_ = v___x_1453_;
goto v___jp_1434_;
}
}
v___jp_1434_:
{
lean_object* v___x_1436_; 
v___x_1436_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___y_1435_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = l_Lean_mkApp3(v_a_1437_, v_u_1417_, v_v_1418_, v_huv_1420_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_dec_ref(v_huv_1420_);
lean_dec_ref(v_v_1418_);
lean_dec_ref(v_u_1417_);
return v___x_1436_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1417_ = stack[0].m_obj;
lean_object* v_v_1418_ = stack[1].m_obj;
lean_object* v_k_1419_ = stack[2].m_obj;
lean_object* v_huv_1420_ = stack[3].m_obj;
lean_object* v_k_x27_1421_ = stack[4].m_obj;
lean_object* v_a_1422_ = stack[5].m_obj;
lean_object* v_a_1423_ = stack[6].m_obj;
lean_object* v_a_1424_ = stack[7].m_obj;
lean_object* v_a_1425_ = stack[8].m_obj;
lean_object* v_a_1426_ = stack[9].m_obj;
lean_object* v_a_1427_ = stack[10].m_obj;
lean_object* v_a_1428_ = stack[11].m_obj;
lean_object* v_a_1429_ = stack[12].m_obj;
lean_object* v_a_1430_ = stack[13].m_obj;
lean_object* v_a_1431_ = stack[14].m_obj;
lean_object* v_a_1432_ = stack[15].m_obj;
lean_object* v_res_1454_;
v_res_1454_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1417_, v_v_1418_, v_k_1419_, v_huv_1420_, v_k_x27_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
stack->m_obj
 = v_res_1454_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___boxed(lean_object** _args){
lean_object* v_u_1455_ = _args[0];
lean_object* v_v_1456_ = _args[1];
lean_object* v_k_1457_ = _args[2];
lean_object* v_huv_1458_ = _args[3];
lean_object* v_k_x27_1459_ = _args[4];
lean_object* v_a_1460_ = _args[5];
lean_object* v_a_1461_ = _args[6];
lean_object* v_a_1462_ = _args[7];
lean_object* v_a_1463_ = _args[8];
lean_object* v_a_1464_ = _args[9];
lean_object* v_a_1465_ = _args[10];
lean_object* v_a_1466_ = _args[11];
lean_object* v_a_1467_ = _args[12];
lean_object* v_a_1468_ = _args[13];
lean_object* v_a_1469_ = _args[14];
lean_object* v_a_1470_ = _args[15];
lean_object* v_a_1471_ = _args[16];
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1455_, v_v_1456_, v_k_1457_, v_huv_1458_, v_k_x27_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_k_x27_1459_);
lean_dec_ref(v_k_1457_);
return v_res_1472_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(lean_object* v_u_1497_, lean_object* v_v_1498_, lean_object* v_k_1499_, lean_object* v_huv_1500_, lean_object* v_k_x27_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v_k_1521_; uint8_t v_strict_1522_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1538_; 
v_k_1521_ = lean_ctor_get(v_k_x27_1501_, 0);
v_strict_1522_ = lean_ctor_get_uint8(v_k_x27_1501_, sizeof(void*)*1);
if (v_strict_1522_ == 0)
{
uint8_t v_strict_1553_; 
v_strict_1553_ = lean_ctor_get_uint8(v_k_1499_, sizeof(void*)*1);
if (v_strict_1553_ == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1));
v___y_1538_ = v___x_1554_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3));
v___y_1538_ = v___x_1555_;
goto v___jp_1537_;
}
}
else
{
uint8_t v_strict_1556_; 
v_strict_1556_ = lean_ctor_get_uint8(v_k_1499_, sizeof(void*)*1);
if (v_strict_1556_ == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5));
v___y_1538_ = v___x_1557_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7));
v___y_1538_ = v___x_1558_;
goto v___jp_1537_;
}
}
v___jp_1514_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = l_Lean_eagerReflBoolTrue;
v___x_1519_ = l_Lean_mkApp6(v___y_1515_, v_u_1497_, v_v_1498_, v___y_1516_, v___y_1517_, v___x_1518_, v_huv_1500_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
v___jp_1523_:
{
lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1527_ = lean_int_dec_le(v___x_1526_, v_k_1521_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1531_ = lean_int_neg(v_k_1521_);
v___x_1532_ = l_Int_toNat(v___x_1531_);
lean_dec(v___x_1531_);
v___x_1533_ = l_Lean_instToExprInt_mkNat(v___x_1532_);
v___x_1534_ = l_Lean_mkApp3(v___x_1528_, v___x_1529_, v___x_1530_, v___x_1533_);
v___y_1515_ = v___y_1524_;
v___y_1516_ = v___y_1525_;
v___y_1517_ = v___x_1534_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = l_Int_toNat(v_k_1521_);
v___x_1536_ = l_Lean_instToExprInt_mkNat(v___x_1535_);
v___y_1515_ = v___y_1524_;
v___y_1516_ = v___y_1525_;
v___y_1517_ = v___x_1536_;
goto v___jp_1514_;
}
}
v___jp_1537_:
{
lean_object* v___x_1539_; 
lean_inc(v___y_1538_);
v___x_1539_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1538_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v_k_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v_k_1541_ = lean_ctor_get(v_k_1499_, 0);
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1543_ = lean_int_dec_le(v___x_1542_, v_k_1541_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1547_ = lean_int_neg(v_k_1541_);
v___x_1548_ = l_Int_toNat(v___x_1547_);
lean_dec(v___x_1547_);
v___x_1549_ = l_Lean_instToExprInt_mkNat(v___x_1548_);
v___x_1550_ = l_Lean_mkApp3(v___x_1544_, v___x_1545_, v___x_1546_, v___x_1549_);
v___y_1524_ = v_a_1540_;
v___y_1525_ = v___x_1550_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Int_toNat(v_k_1541_);
v___x_1552_ = l_Lean_instToExprInt_mkNat(v___x_1551_);
v___y_1524_ = v_a_1540_;
v___y_1525_ = v___x_1552_;
goto v___jp_1523_;
}
}
else
{
lean_dec_ref(v_huv_1500_);
lean_dec_ref(v_v_1498_);
lean_dec_ref(v_u_1497_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1497_ = stack[0].m_obj;
lean_object* v_v_1498_ = stack[1].m_obj;
lean_object* v_k_1499_ = stack[2].m_obj;
lean_object* v_huv_1500_ = stack[3].m_obj;
lean_object* v_k_x27_1501_ = stack[4].m_obj;
lean_object* v_a_1502_ = stack[5].m_obj;
lean_object* v_a_1503_ = stack[6].m_obj;
lean_object* v_a_1504_ = stack[7].m_obj;
lean_object* v_a_1505_ = stack[8].m_obj;
lean_object* v_a_1506_ = stack[9].m_obj;
lean_object* v_a_1507_ = stack[10].m_obj;
lean_object* v_a_1508_ = stack[11].m_obj;
lean_object* v_a_1509_ = stack[12].m_obj;
lean_object* v_a_1510_ = stack[13].m_obj;
lean_object* v_a_1511_ = stack[14].m_obj;
lean_object* v_a_1512_ = stack[15].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1497_, v_v_1498_, v_k_1499_, v_huv_1500_, v_k_x27_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(lean_object** _args){
lean_object* v_u_1560_ = _args[0];
lean_object* v_v_1561_ = _args[1];
lean_object* v_k_1562_ = _args[2];
lean_object* v_huv_1563_ = _args[3];
lean_object* v_k_x27_1564_ = _args[4];
lean_object* v_a_1565_ = _args[5];
lean_object* v_a_1566_ = _args[6];
lean_object* v_a_1567_ = _args[7];
lean_object* v_a_1568_ = _args[8];
lean_object* v_a_1569_ = _args[9];
lean_object* v_a_1570_ = _args[10];
lean_object* v_a_1571_ = _args[11];
lean_object* v_a_1572_ = _args[12];
lean_object* v_a_1573_ = _args[13];
lean_object* v_a_1574_ = _args[14];
lean_object* v_a_1575_ = _args[15];
lean_object* v_a_1576_ = _args[16];
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1560_, v_v_1561_, v_k_1562_, v_huv_1563_, v_k_x27_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_k_x27_1564_);
lean_dec_ref(v_k_1562_);
return v_res_1577_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object* v_u_1578_, lean_object* v_v_1579_, lean_object* v_k_1580_, lean_object* v_huv_1581_, lean_object* v_k_x27_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_Grind_Order_isRing(v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = lean_unbox(v_a_1596_);
lean_dec(v_a_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1578_, v_v_1579_, v_k_1580_, v_huv_1581_, v_k_x27_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1578_, v_v_1579_, v_k_1580_, v_huv_1581_, v_k_x27_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
return v___x_1599_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_huv_1581_);
lean_dec_ref(v_v_1579_);
lean_dec_ref(v_u_1578_);
v_a_1600_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1595_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1595_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1578_ = stack[0].m_obj;
lean_object* v_v_1579_ = stack[1].m_obj;
lean_object* v_k_1580_ = stack[2].m_obj;
lean_object* v_huv_1581_ = stack[3].m_obj;
lean_object* v_k_x27_1582_ = stack[4].m_obj;
lean_object* v_a_1583_ = stack[5].m_obj;
lean_object* v_a_1584_ = stack[6].m_obj;
lean_object* v_a_1585_ = stack[7].m_obj;
lean_object* v_a_1586_ = stack[8].m_obj;
lean_object* v_a_1587_ = stack[9].m_obj;
lean_object* v_a_1588_ = stack[10].m_obj;
lean_object* v_a_1589_ = stack[11].m_obj;
lean_object* v_a_1590_ = stack[12].m_obj;
lean_object* v_a_1591_ = stack[13].m_obj;
lean_object* v_a_1592_ = stack[14].m_obj;
lean_object* v_a_1593_ = stack[15].m_obj;
lean_object* v_res_1608_;
v_res_1608_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_u_1578_, v_v_1579_, v_k_1580_, v_huv_1581_, v_k_x27_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
stack->m_obj
 = v_res_1608_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof___boxed(lean_object** _args){
lean_object* v_u_1609_ = _args[0];
lean_object* v_v_1610_ = _args[1];
lean_object* v_k_1611_ = _args[2];
lean_object* v_huv_1612_ = _args[3];
lean_object* v_k_x27_1613_ = _args[4];
lean_object* v_a_1614_ = _args[5];
lean_object* v_a_1615_ = _args[6];
lean_object* v_a_1616_ = _args[7];
lean_object* v_a_1617_ = _args[8];
lean_object* v_a_1618_ = _args[9];
lean_object* v_a_1619_ = _args[10];
lean_object* v_a_1620_ = _args[11];
lean_object* v_a_1621_ = _args[12];
lean_object* v_a_1622_ = _args[13];
lean_object* v_a_1623_ = _args[14];
lean_object* v_a_1624_ = _args[15];
lean_object* v_a_1625_ = _args[16];
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_u_1609_, v_v_1610_, v_k_1611_, v_huv_1612_, v_k_x27_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_k_x27_1613_);
lean_dec_ref(v_k_1611_);
return v_res_1626_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(lean_object* v_u_1639_, lean_object* v_k_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v_k_1659_; uint8_t v_strict_1660_; lean_object* v___y_1662_; 
v_k_1659_ = lean_ctor_get(v_k_1640_, 0);
v_strict_1660_ = lean_ctor_get_uint8(v_k_1640_, sizeof(void*)*1);
if (v_strict_1660_ == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1));
v___y_1662_ = v___x_1676_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3));
v___y_1662_ = v___x_1677_;
goto v___jp_1661_;
}
v___jp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = l_Lean_eagerReflBoolTrue;
v___x_1657_ = l_Lean_mkApp3(v___y_1654_, v_u_1639_, v___y_1655_, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
v___jp_1661_:
{
lean_object* v___x_1663_; 
lean_inc(v___y_1662_);
v___x_1663_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1662_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1666_ = lean_int_dec_le(v___x_1665_, v_k_1659_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1670_ = lean_int_neg(v_k_1659_);
v___x_1671_ = l_Int_toNat(v___x_1670_);
lean_dec(v___x_1670_);
v___x_1672_ = l_Lean_instToExprInt_mkNat(v___x_1671_);
v___x_1673_ = l_Lean_mkApp3(v___x_1667_, v___x_1668_, v___x_1669_, v___x_1672_);
v___y_1654_ = v_a_1664_;
v___y_1655_ = v___x_1673_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = l_Int_toNat(v_k_1659_);
v___x_1675_ = l_Lean_instToExprInt_mkNat(v___x_1674_);
v___y_1654_ = v_a_1664_;
v___y_1655_ = v___x_1675_;
goto v___jp_1653_;
}
}
else
{
lean_dec_ref(v_u_1639_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1639_ = stack[0].m_obj;
lean_object* v_k_1640_ = stack[1].m_obj;
lean_object* v_a_1641_ = stack[2].m_obj;
lean_object* v_a_1642_ = stack[3].m_obj;
lean_object* v_a_1643_ = stack[4].m_obj;
lean_object* v_a_1644_ = stack[5].m_obj;
lean_object* v_a_1645_ = stack[6].m_obj;
lean_object* v_a_1646_ = stack[7].m_obj;
lean_object* v_a_1647_ = stack[8].m_obj;
lean_object* v_a_1648_ = stack[9].m_obj;
lean_object* v_a_1649_ = stack[10].m_obj;
lean_object* v_a_1650_ = stack[11].m_obj;
lean_object* v_a_1651_ = stack[12].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1639_, v_k_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(lean_object* v_u_1679_, lean_object* v_k_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1679_, v_k_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_k_1680_);
return v_res_1693_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(lean_object* v_u_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1));
v___x_1714_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_1713_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = l_Lean_Expr_app___override(v_a_1715_, v_u_1700_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_dec_ref(v_u_1700_);
return v___x_1714_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1700_ = stack[0].m_obj;
lean_object* v_a_1701_ = stack[1].m_obj;
lean_object* v_a_1702_ = stack[2].m_obj;
lean_object* v_a_1703_ = stack[3].m_obj;
lean_object* v_a_1704_ = stack[4].m_obj;
lean_object* v_a_1705_ = stack[5].m_obj;
lean_object* v_a_1706_ = stack[6].m_obj;
lean_object* v_a_1707_ = stack[7].m_obj;
lean_object* v_a_1708_ = stack[8].m_obj;
lean_object* v_a_1709_ = stack[9].m_obj;
lean_object* v_a_1710_ = stack[10].m_obj;
lean_object* v_a_1711_ = stack[11].m_obj;
lean_object* v_res_1724_;
v_res_1724_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
stack->m_obj
 = v_res_1724_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___boxed(lean_object* v_u_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec(v_a_1726_);
return v_res_1738_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1741_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1));
v___x_1742_ = lean_unsigned_to_nat(4u);
v___x_1743_ = lean_unsigned_to_nat(228u);
v___x_1744_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0));
v___x_1745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1746_ = l_mkPanicMessageWithDecl(v___x_1745_, v___x_1744_, v___x_1743_, v___x_1742_, v___x_1741_);
return v___x_1746_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object* v_u_1747_, lean_object* v_k_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Meta_Grind_Order_isRing(v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; uint8_t v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = lean_unbox(v_a_1762_);
lean_dec(v_a_1762_);
if (v___x_1763_ == 0)
{
uint8_t v_strict_1764_; 
v_strict_1764_ = lean_ctor_get_uint8(v_k_1748_, sizeof(void*)*1);
if (v_strict_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec_ref(v_u_1747_);
v___x_1765_ = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2);
v___x_1766_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1765_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1747_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
return v___x_1767_;
}
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1747_, v_k_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
return v___x_1768_;
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_u_1747_);
v_a_1769_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1761_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1761_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1747_ = stack[0].m_obj;
lean_object* v_k_1748_ = stack[1].m_obj;
lean_object* v_a_1749_ = stack[2].m_obj;
lean_object* v_a_1750_ = stack[3].m_obj;
lean_object* v_a_1751_ = stack[4].m_obj;
lean_object* v_a_1752_ = stack[5].m_obj;
lean_object* v_a_1753_ = stack[6].m_obj;
lean_object* v_a_1754_ = stack[7].m_obj;
lean_object* v_a_1755_ = stack[8].m_obj;
lean_object* v_a_1756_ = stack[9].m_obj;
lean_object* v_a_1757_ = stack[10].m_obj;
lean_object* v_a_1758_ = stack[11].m_obj;
lean_object* v_a_1759_ = stack[12].m_obj;
lean_object* v_res_1777_;
v_res_1777_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_u_1747_, v_k_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
stack->m_obj
 = v_res_1777_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___boxed(lean_object* v_u_1778_, lean_object* v_k_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_u_1778_, v_k_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_k_1779_);
return v_res_1792_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(lean_object* v_u_1799_, lean_object* v_h_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
v___x_1814_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_1813_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = l_Lean_mkAppB(v_a_1815_, v_u_1799_, v_h_1800_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_dec_ref(v_h_1800_);
lean_dec_ref(v_u_1799_);
return v___x_1814_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1799_ = stack[0].m_obj;
lean_object* v_h_1800_ = stack[1].m_obj;
lean_object* v_a_1801_ = stack[2].m_obj;
lean_object* v_a_1802_ = stack[3].m_obj;
lean_object* v_a_1803_ = stack[4].m_obj;
lean_object* v_a_1804_ = stack[5].m_obj;
lean_object* v_a_1805_ = stack[6].m_obj;
lean_object* v_a_1806_ = stack[7].m_obj;
lean_object* v_a_1807_ = stack[8].m_obj;
lean_object* v_a_1808_ = stack[9].m_obj;
lean_object* v_a_1809_ = stack[10].m_obj;
lean_object* v_a_1810_ = stack[11].m_obj;
lean_object* v_a_1811_ = stack[12].m_obj;
lean_object* v_res_1824_;
v_res_1824_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_1799_, v_h_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
stack->m_obj
 = v_res_1824_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___boxed(lean_object* v_u_1825_, lean_object* v_h_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_1825_, v_h_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec(v_a_1827_);
return v_res_1839_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(lean_object* v_u_1852_, lean_object* v_k_1853_, lean_object* v_h_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v_k_1873_; uint8_t v_strict_1874_; lean_object* v___y_1876_; 
v_k_1873_ = lean_ctor_get(v_k_1853_, 0);
v_strict_1874_ = lean_ctor_get_uint8(v_k_1853_, sizeof(void*)*1);
if (v_strict_1874_ == 0)
{
lean_object* v___x_1890_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
v___y_1876_ = v___x_1890_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1891_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
v___y_1876_ = v___x_1891_;
goto v___jp_1875_;
}
v___jp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = l_Lean_eagerReflBoolTrue;
v___x_1871_ = l_Lean_mkApp4(v___y_1868_, v_u_1852_, v___y_1869_, v___x_1870_, v_h_1854_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
v___jp_1875_:
{
lean_object* v___x_1877_; 
lean_inc(v___y_1876_);
v___x_1877_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1876_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1880_ = lean_int_dec_le(v___x_1879_, v_k_1873_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1884_ = lean_int_neg(v_k_1873_);
v___x_1885_ = l_Int_toNat(v___x_1884_);
lean_dec(v___x_1884_);
v___x_1886_ = l_Lean_instToExprInt_mkNat(v___x_1885_);
v___x_1887_ = l_Lean_mkApp3(v___x_1881_, v___x_1882_, v___x_1883_, v___x_1886_);
v___y_1868_ = v_a_1878_;
v___y_1869_ = v___x_1887_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = l_Int_toNat(v_k_1873_);
v___x_1889_ = l_Lean_instToExprInt_mkNat(v___x_1888_);
v___y_1868_ = v_a_1878_;
v___y_1869_ = v___x_1889_;
goto v___jp_1867_;
}
}
else
{
lean_dec_ref(v_h_1854_);
lean_dec_ref(v_u_1852_);
return v___x_1877_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1852_ = stack[0].m_obj;
lean_object* v_k_1853_ = stack[1].m_obj;
lean_object* v_h_1854_ = stack[2].m_obj;
lean_object* v_a_1855_ = stack[3].m_obj;
lean_object* v_a_1856_ = stack[4].m_obj;
lean_object* v_a_1857_ = stack[5].m_obj;
lean_object* v_a_1858_ = stack[6].m_obj;
lean_object* v_a_1859_ = stack[7].m_obj;
lean_object* v_a_1860_ = stack[8].m_obj;
lean_object* v_a_1861_ = stack[9].m_obj;
lean_object* v_a_1862_ = stack[10].m_obj;
lean_object* v_a_1863_ = stack[11].m_obj;
lean_object* v_a_1864_ = stack[12].m_obj;
lean_object* v_a_1865_ = stack[13].m_obj;
lean_object* v_res_1892_;
v_res_1892_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_1852_, v_k_1853_, v_h_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
stack->m_obj
 = v_res_1892_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(lean_object* v_u_1893_, lean_object* v_k_1894_, lean_object* v_h_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_1893_, v_k_1894_, v_h_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_k_1894_);
return v_res_1908_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object* v_u_1909_, lean_object* v_k_1910_, lean_object* v_h_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Meta_Grind_Order_isRing(v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; uint8_t v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = lean_unbox(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_1909_, v_h_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_1909_, v_k_1910_, v_h_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
return v___x_1928_;
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_h_1911_);
lean_dec_ref(v_u_1909_);
v_a_1929_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1924_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1924_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkSelfUnsatProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1909_ = stack[0].m_obj;
lean_object* v_k_1910_ = stack[1].m_obj;
lean_object* v_h_1911_ = stack[2].m_obj;
lean_object* v_a_1912_ = stack[3].m_obj;
lean_object* v_a_1913_ = stack[4].m_obj;
lean_object* v_a_1914_ = stack[5].m_obj;
lean_object* v_a_1915_ = stack[6].m_obj;
lean_object* v_a_1916_ = stack[7].m_obj;
lean_object* v_a_1917_ = stack[8].m_obj;
lean_object* v_a_1918_ = stack[9].m_obj;
lean_object* v_a_1919_ = stack[10].m_obj;
lean_object* v_a_1920_ = stack[11].m_obj;
lean_object* v_a_1921_ = stack[12].m_obj;
lean_object* v_a_1922_ = stack[13].m_obj;
lean_object* v_res_1937_;
v_res_1937_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_u_1909_, v_k_1910_, v_h_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
stack->m_obj
 = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof___boxed(lean_object* v_u_1938_, lean_object* v_k_1939_, lean_object* v_h_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_u_1938_, v_k_1939_, v_h_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_k_1939_);
return v_res_1953_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1));
v___x_1957_ = lean_unsigned_to_nat(2u);
v___x_1958_ = lean_unsigned_to_nat(255u);
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0));
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1961_ = l_mkPanicMessageWithDecl(v___x_1960_, v___x_1959_, v___x_1958_, v___x_1957_, v___x_1956_);
return v___x_1961_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(lean_object* v_u_1962_, lean_object* v_v_1963_, lean_object* v_k_u2081_1964_, lean_object* v_h_u2081_1965_, lean_object* v_k_u2082_1966_, lean_object* v_h_u2082_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
uint8_t v_strict_1980_; uint8_t v_strict_1981_; lean_object* v___x_1982_; 
v_strict_1980_ = lean_ctor_get_uint8(v_k_u2081_1964_, sizeof(void*)*1);
v_strict_1981_ = lean_ctor_get_uint8(v_k_u2082_1966_, sizeof(void*)*1);
lean_inc_ref_n(v_u_1962_, 2);
v___x_1982_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_1962_, v_v_1963_, v_u_1962_, v_strict_1980_, v_strict_1981_, v_h_u2081_1965_, v_h_u2082_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
if (v_strict_1980_ == 0)
{
if (v_strict_1981_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v_a_1983_);
lean_dec_ref(v_u_1962_);
v___x_1996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2);
v___x_1997_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1996_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1997_;
}
else
{
goto v___jp_1984_;
}
}
else
{
goto v___jp_1984_;
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
v___x_1986_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_1985_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = l_Lean_mkAppB(v_a_1987_, v_u_1962_, v_a_1983_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_1991_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_dec(v_a_1983_);
lean_dec_ref(v_u_1962_);
return v___x_1986_;
}
}
}
else
{
lean_dec_ref(v_u_1962_);
return v___x_1982_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1962_ = stack[0].m_obj;
lean_object* v_v_1963_ = stack[1].m_obj;
lean_object* v_k_u2081_1964_ = stack[2].m_obj;
lean_object* v_h_u2081_1965_ = stack[3].m_obj;
lean_object* v_k_u2082_1966_ = stack[4].m_obj;
lean_object* v_h_u2082_1967_ = stack[5].m_obj;
lean_object* v_a_1968_ = stack[6].m_obj;
lean_object* v_a_1969_ = stack[7].m_obj;
lean_object* v_a_1970_ = stack[8].m_obj;
lean_object* v_a_1971_ = stack[9].m_obj;
lean_object* v_a_1972_ = stack[10].m_obj;
lean_object* v_a_1973_ = stack[11].m_obj;
lean_object* v_a_1974_ = stack[12].m_obj;
lean_object* v_a_1975_ = stack[13].m_obj;
lean_object* v_a_1976_ = stack[14].m_obj;
lean_object* v_a_1977_ = stack[15].m_obj;
lean_object* v_a_1978_ = stack[16].m_obj;
lean_object* v_res_1998_;
v_res_1998_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_1962_, v_v_1963_, v_k_u2081_1964_, v_h_u2081_1965_, v_k_u2082_1966_, v_h_u2082_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
stack->m_obj
 = v_res_1998_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___boxed(lean_object** _args){
lean_object* v_u_1999_ = _args[0];
lean_object* v_v_2000_ = _args[1];
lean_object* v_k_u2081_2001_ = _args[2];
lean_object* v_h_u2081_2002_ = _args[3];
lean_object* v_k_u2082_2003_ = _args[4];
lean_object* v_h_u2082_2004_ = _args[5];
lean_object* v_a_2005_ = _args[6];
lean_object* v_a_2006_ = _args[7];
lean_object* v_a_2007_ = _args[8];
lean_object* v_a_2008_ = _args[9];
lean_object* v_a_2009_ = _args[10];
lean_object* v_a_2010_ = _args[11];
lean_object* v_a_2011_ = _args[12];
lean_object* v_a_2012_ = _args[13];
lean_object* v_a_2013_ = _args[14];
lean_object* v_a_2014_ = _args[15];
lean_object* v_a_2015_ = _args[16];
lean_object* v_a_2016_ = _args[17];
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_1999_, v_v_2000_, v_k_u2081_2001_, v_h_u2081_2002_, v_k_u2082_2003_, v_h_u2082_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_k_u2082_2003_);
lean_dec_ref(v_k_u2081_2001_);
return v_res_2017_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(lean_object* v_u_2018_, lean_object* v_v_2019_, lean_object* v_k_u2081_2020_, lean_object* v_h_u2081_2021_, lean_object* v_k_u2082_2022_, lean_object* v_h_u2082_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; 
lean_inc_ref_n(v_u_2018_, 2);
v___x_2036_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_2018_, v_v_2019_, v_u_2018_, v_k_u2081_2020_, v_k_u2082_2022_, v_h_u2081_2021_, v_h_u2082_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2072_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2072_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2072_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v_k_2049_; uint8_t v_strict_2050_; lean_object* v___y_2052_; 
v_k_2049_ = lean_ctor_get(v_k_u2081_2020_, 0);
v_strict_2050_ = lean_ctor_get_uint8(v_k_u2081_2020_, sizeof(void*)*1);
if (v_strict_2050_ == 0)
{
uint8_t v_strict_2070_; 
v_strict_2070_ = lean_ctor_get_uint8(v_k_u2082_2022_, sizeof(void*)*1);
if (v_strict_2070_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
v___y_2052_ = v___x_2071_;
goto v___jp_2051_;
}
else
{
goto v___jp_2068_;
}
}
else
{
goto v___jp_2068_;
}
v___jp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = l_Lean_eagerReflBoolTrue;
v___x_2045_ = l_Lean_mkApp4(v___y_2042_, v_u_2018_, v___y_2043_, v___x_2044_, v_a_2037_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2045_);
v___x_2047_ = v___x_2039_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
v___jp_2051_:
{
lean_object* v___x_2053_; 
lean_inc(v___y_2052_);
v___x_2053_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_2052_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v_k_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v_k_2055_ = lean_ctor_get(v_k_u2082_2022_, 0);
v___x_2056_ = lean_int_add(v_k_2049_, v_k_2055_);
v___x_2057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_2058_ = lean_int_dec_le(v___x_2057_, v___x_2056_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_2060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_2061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_2062_ = lean_int_neg(v___x_2056_);
lean_dec(v___x_2056_);
v___x_2063_ = l_Int_toNat(v___x_2062_);
lean_dec(v___x_2062_);
v___x_2064_ = l_Lean_instToExprInt_mkNat(v___x_2063_);
v___x_2065_ = l_Lean_mkApp3(v___x_2059_, v___x_2060_, v___x_2061_, v___x_2064_);
v___y_2042_ = v_a_2054_;
v___y_2043_ = v___x_2065_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = l_Int_toNat(v___x_2056_);
lean_dec(v___x_2056_);
v___x_2067_ = l_Lean_instToExprInt_mkNat(v___x_2066_);
v___y_2042_ = v_a_2054_;
v___y_2043_ = v___x_2067_;
goto v___jp_2041_;
}
}
else
{
lean_del_object(v___x_2039_);
lean_dec(v_a_2037_);
lean_dec_ref(v_u_2018_);
return v___x_2053_;
}
}
v___jp_2068_:
{
lean_object* v___x_2069_; 
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
v___y_2052_ = v___x_2069_;
goto v___jp_2051_;
}
}
}
else
{
lean_dec_ref(v_u_2018_);
return v___x_2036_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2018_ = stack[0].m_obj;
lean_object* v_v_2019_ = stack[1].m_obj;
lean_object* v_k_u2081_2020_ = stack[2].m_obj;
lean_object* v_h_u2081_2021_ = stack[3].m_obj;
lean_object* v_k_u2082_2022_ = stack[4].m_obj;
lean_object* v_h_u2082_2023_ = stack[5].m_obj;
lean_object* v_a_2024_ = stack[6].m_obj;
lean_object* v_a_2025_ = stack[7].m_obj;
lean_object* v_a_2026_ = stack[8].m_obj;
lean_object* v_a_2027_ = stack[9].m_obj;
lean_object* v_a_2028_ = stack[10].m_obj;
lean_object* v_a_2029_ = stack[11].m_obj;
lean_object* v_a_2030_ = stack[12].m_obj;
lean_object* v_a_2031_ = stack[13].m_obj;
lean_object* v_a_2032_ = stack[14].m_obj;
lean_object* v_a_2033_ = stack[15].m_obj;
lean_object* v_a_2034_ = stack[16].m_obj;
lean_object* v_res_2073_;
v_res_2073_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2018_, v_v_2019_, v_k_u2081_2020_, v_h_u2081_2021_, v_k_u2082_2022_, v_h_u2082_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
stack->m_obj
 = v_res_2073_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset___boxed(lean_object** _args){
lean_object* v_u_2074_ = _args[0];
lean_object* v_v_2075_ = _args[1];
lean_object* v_k_u2081_2076_ = _args[2];
lean_object* v_h_u2081_2077_ = _args[3];
lean_object* v_k_u2082_2078_ = _args[4];
lean_object* v_h_u2082_2079_ = _args[5];
lean_object* v_a_2080_ = _args[6];
lean_object* v_a_2081_ = _args[7];
lean_object* v_a_2082_ = _args[8];
lean_object* v_a_2083_ = _args[9];
lean_object* v_a_2084_ = _args[10];
lean_object* v_a_2085_ = _args[11];
lean_object* v_a_2086_ = _args[12];
lean_object* v_a_2087_ = _args[13];
lean_object* v_a_2088_ = _args[14];
lean_object* v_a_2089_ = _args[15];
lean_object* v_a_2090_ = _args[16];
lean_object* v_a_2091_ = _args[17];
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2074_, v_v_2075_, v_k_u2081_2076_, v_h_u2081_2077_, v_k_u2082_2078_, v_h_u2082_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_k_u2082_2078_);
lean_dec_ref(v_k_u2081_2076_);
return v_res_2092_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object* v_u_2093_, lean_object* v_v_2094_, lean_object* v_k_u2081_2095_, lean_object* v_h_u2081_2096_, lean_object* v_k_u2082_2097_, lean_object* v_h_u2082_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Meta_Grind_Order_isRing(v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = lean_unbox(v_a_2112_);
lean_dec(v_a_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_2093_, v_v_2094_, v_k_u2081_2095_, v_h_u2081_2096_, v_k_u2082_2097_, v_h_u2082_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; 
v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2093_, v_v_2094_, v_k_u2081_2095_, v_h_u2081_2096_, v_k_u2082_2097_, v_h_u2082_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2115_;
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_h_u2082_2098_);
lean_dec_ref(v_h_u2081_2096_);
lean_dec_ref(v_v_2094_);
lean_dec_ref(v_u_2093_);
v_a_2116_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2111_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2111_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkUnsatProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2093_ = stack[0].m_obj;
lean_object* v_v_2094_ = stack[1].m_obj;
lean_object* v_k_u2081_2095_ = stack[2].m_obj;
lean_object* v_h_u2081_2096_ = stack[3].m_obj;
lean_object* v_k_u2082_2097_ = stack[4].m_obj;
lean_object* v_h_u2082_2098_ = stack[5].m_obj;
lean_object* v_a_2099_ = stack[6].m_obj;
lean_object* v_a_2100_ = stack[7].m_obj;
lean_object* v_a_2101_ = stack[8].m_obj;
lean_object* v_a_2102_ = stack[9].m_obj;
lean_object* v_a_2103_ = stack[10].m_obj;
lean_object* v_a_2104_ = stack[11].m_obj;
lean_object* v_a_2105_ = stack[12].m_obj;
lean_object* v_a_2106_ = stack[13].m_obj;
lean_object* v_a_2107_ = stack[14].m_obj;
lean_object* v_a_2108_ = stack[15].m_obj;
lean_object* v_a_2109_ = stack[16].m_obj;
lean_object* v_res_2124_;
v_res_2124_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_u_2093_, v_v_2094_, v_k_u2081_2095_, v_h_u2081_2096_, v_k_u2082_2097_, v_h_u2082_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
stack->m_obj
 = v_res_2124_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof___boxed(lean_object** _args){
lean_object* v_u_2125_ = _args[0];
lean_object* v_v_2126_ = _args[1];
lean_object* v_k_u2081_2127_ = _args[2];
lean_object* v_h_u2081_2128_ = _args[3];
lean_object* v_k_u2082_2129_ = _args[4];
lean_object* v_h_u2082_2130_ = _args[5];
lean_object* v_a_2131_ = _args[6];
lean_object* v_a_2132_ = _args[7];
lean_object* v_a_2133_ = _args[8];
lean_object* v_a_2134_ = _args[9];
lean_object* v_a_2135_ = _args[10];
lean_object* v_a_2136_ = _args[11];
lean_object* v_a_2137_ = _args[12];
lean_object* v_a_2138_ = _args[13];
lean_object* v_a_2139_ = _args[14];
lean_object* v_a_2140_ = _args[15];
lean_object* v_a_2141_ = _args[16];
lean_object* v_a_2142_ = _args[17];
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_u_2125_, v_v_2126_, v_k_u2081_2127_, v_h_u2081_2128_, v_k_u2082_2129_, v_h_u2082_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_k_u2082_2129_);
lean_dec_ref(v_k_u2081_2127_);
return v_res_2143_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(lean_object* v_u_2150_, lean_object* v_v_2151_, lean_object* v_h_u2081_2152_, lean_object* v_h_u2082_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1));
v___x_2167_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_2166_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2176_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = l_Lean_mkApp4(v_a_2168_, v_u_2150_, v_v_2151_, v_h_u2081_2152_, v_h_u2082_2153_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2172_);
v___x_2174_ = v___x_2170_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_dec_ref(v_h_u2082_2153_);
lean_dec_ref(v_h_u2081_2152_);
lean_dec_ref(v_v_2151_);
lean_dec_ref(v_u_2150_);
return v___x_2167_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2150_ = stack[0].m_obj;
lean_object* v_v_2151_ = stack[1].m_obj;
lean_object* v_h_u2081_2152_ = stack[2].m_obj;
lean_object* v_h_u2082_2153_ = stack[3].m_obj;
lean_object* v_a_2154_ = stack[4].m_obj;
lean_object* v_a_2155_ = stack[5].m_obj;
lean_object* v_a_2156_ = stack[6].m_obj;
lean_object* v_a_2157_ = stack[7].m_obj;
lean_object* v_a_2158_ = stack[8].m_obj;
lean_object* v_a_2159_ = stack[9].m_obj;
lean_object* v_a_2160_ = stack[10].m_obj;
lean_object* v_a_2161_ = stack[11].m_obj;
lean_object* v_a_2162_ = stack[12].m_obj;
lean_object* v_a_2163_ = stack[13].m_obj;
lean_object* v_a_2164_ = stack[14].m_obj;
lean_object* v_res_2177_;
v_res_2177_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2150_, v_v_2151_, v_h_u2081_2152_, v_h_u2082_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
stack->m_obj
 = v_res_2177_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___boxed(lean_object* v_u_2178_, lean_object* v_v_2179_, lean_object* v_h_u2081_2180_, lean_object* v_h_u2082_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2178_, v_v_2179_, v_h_u2081_2180_, v_h_u2082_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec(v_a_2182_);
return v_res_2194_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(lean_object* v_u_2201_, lean_object* v_v_2202_, lean_object* v_h_u2081_2203_, lean_object* v_h_u2082_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1));
v___x_2218_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_2217_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2220_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = l_Lean_Meta_Grind_Order_getOrder(v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2236_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2236_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2236_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___y_2226_; lean_object* v_ringInst_x3f_2232_; 
v_ringInst_x3f_2232_ = lean_ctor_get(v_a_2221_, 11);
lean_inc(v_ringInst_x3f_2232_);
lean_dec(v_a_2221_);
if (lean_obj_tag(v_ringInst_x3f_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_2234_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2233_);
v___y_2226_ = v___x_2234_;
goto v___jp_2225_;
}
else
{
lean_object* v_val_2235_; 
v_val_2235_ = lean_ctor_get(v_ringInst_x3f_2232_, 0);
lean_inc(v_val_2235_);
lean_dec_ref_known(v_ringInst_x3f_2232_, 1);
v___y_2226_ = v_val_2235_;
goto v___jp_2225_;
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = l_Lean_Expr_app___override(v_a_2219_, v___y_2226_);
v___x_2228_ = l_Lean_mkApp4(v___x_2227_, v_u_2201_, v_v_2202_, v_h_u2081_2203_, v_h_u2082_2204_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2228_);
v___x_2230_ = v___x_2223_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2219_);
lean_dec_ref(v_h_u2082_2204_);
lean_dec_ref(v_h_u2081_2203_);
lean_dec_ref(v_v_2202_);
lean_dec_ref(v_u_2201_);
v_a_2237_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2220_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2220_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2082_2204_);
lean_dec_ref(v_h_u2081_2203_);
lean_dec_ref(v_v_2202_);
lean_dec_ref(v_u_2201_);
return v___x_2218_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2201_ = stack[0].m_obj;
lean_object* v_v_2202_ = stack[1].m_obj;
lean_object* v_h_u2081_2203_ = stack[2].m_obj;
lean_object* v_h_u2082_2204_ = stack[3].m_obj;
lean_object* v_a_2205_ = stack[4].m_obj;
lean_object* v_a_2206_ = stack[5].m_obj;
lean_object* v_a_2207_ = stack[6].m_obj;
lean_object* v_a_2208_ = stack[7].m_obj;
lean_object* v_a_2209_ = stack[8].m_obj;
lean_object* v_a_2210_ = stack[9].m_obj;
lean_object* v_a_2211_ = stack[10].m_obj;
lean_object* v_a_2212_ = stack[11].m_obj;
lean_object* v_a_2213_ = stack[12].m_obj;
lean_object* v_a_2214_ = stack[13].m_obj;
lean_object* v_a_2215_ = stack[14].m_obj;
lean_object* v_res_2245_;
v_res_2245_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2201_, v_v_2202_, v_h_u2081_2203_, v_h_u2082_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___boxed(lean_object* v_u_2246_, lean_object* v_v_2247_, lean_object* v_h_u2081_2248_, lean_object* v_h_u2082_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2246_, v_v_2247_, v_h_u2081_2248_, v_h_u2082_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec(v_a_2250_);
return v_res_2262_;
}
}
lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object* v_u_2263_, lean_object* v_v_2264_, lean_object* v_h_u2081_2265_, lean_object* v_h_u2082_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Meta_Grind_Order_isRing(v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2263_, v_v_2264_, v_h_u2081_2265_, v_h_u2082_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2263_, v_v_2264_, v_h_u2081_2265_, v_h_u2082_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
return v___x_2283_;
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_h_u2082_2266_);
lean_dec_ref(v_h_u2081_2265_);
lean_dec_ref(v_v_2264_);
lean_dec_ref(v_u_2263_);
v_a_2284_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2279_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2279_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2263_ = stack[0].m_obj;
lean_object* v_v_2264_ = stack[1].m_obj;
lean_object* v_h_u2081_2265_ = stack[2].m_obj;
lean_object* v_h_u2082_2266_ = stack[3].m_obj;
lean_object* v_a_2267_ = stack[4].m_obj;
lean_object* v_a_2268_ = stack[5].m_obj;
lean_object* v_a_2269_ = stack[6].m_obj;
lean_object* v_a_2270_ = stack[7].m_obj;
lean_object* v_a_2271_ = stack[8].m_obj;
lean_object* v_a_2272_ = stack[9].m_obj;
lean_object* v_a_2273_ = stack[10].m_obj;
lean_object* v_a_2274_ = stack[11].m_obj;
lean_object* v_a_2275_ = stack[12].m_obj;
lean_object* v_a_2276_ = stack[13].m_obj;
lean_object* v_a_2277_ = stack[14].m_obj;
lean_object* v_res_2292_;
v_res_2292_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_u_2263_, v_v_2264_, v_h_u2081_2265_, v_h_u2082_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
stack->m_obj
 = v_res_2292_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe___boxed(lean_object* v_u_2293_, lean_object* v_v_2294_, lean_object* v_h_u2081_2295_, lean_object* v_h_u2082_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_u_2293_, v_v_2294_, v_h_u2081_2295_, v_h_u2082_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec(v_a_2297_);
return v_res_2309_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Order(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
}
#ifdef __cplusplus
}
#endif
