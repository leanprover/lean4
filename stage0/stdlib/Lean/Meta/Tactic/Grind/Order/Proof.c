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
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object* v_declName_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix___boxed(lean_object* v_declName_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v_declName_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec(v_a_41_);
lean_dec(v_a_40_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(lean_object* v_msg_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = l_Lean_instInhabitedExpr;
v___x_55_ = lean_panic_fn_borrowed(v___x_54_, v_msg_53_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2));
v___x_60_ = lean_unsigned_to_nat(14u);
v___x_61_ = lean_unsigned_to_nat(22u);
v___x_62_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1));
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0));
v___x_64_ = l_mkPanicMessageWithDecl(v___x_63_, v___x_62_, v___x_61_, v___x_60_, v___x_59_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(lean_object* v_declName_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Grind_Order_getStruct(v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_99_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_99_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_99_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_99_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_type_83_; lean_object* v_u_84_; lean_object* v_leInst_85_; lean_object* v_isPartialInst_x3f_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___y_91_; 
v_type_83_ = lean_ctor_get(v_a_79_, 1);
lean_inc_ref(v_type_83_);
v_u_84_ = lean_ctor_get(v_a_79_, 2);
lean_inc(v_u_84_);
v_leInst_85_ = lean_ctor_get(v_a_79_, 4);
lean_inc_ref(v_leInst_85_);
v_isPartialInst_x3f_86_ = lean_ctor_get(v_a_79_, 6);
lean_inc(v_isPartialInst_x3f_86_);
lean_dec(v_a_79_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v_u_84_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = l_Lean_mkConst(v_declName_65_, v___x_88_);
if (lean_obj_tag(v_isPartialInst_x3f_86_) == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_97_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_96_);
v___y_91_ = v___x_97_;
goto v___jp_90_;
}
else
{
lean_object* v_val_98_; 
v_val_98_ = lean_ctor_get(v_isPartialInst_x3f_86_, 0);
lean_inc(v_val_98_);
lean_dec_ref(v_isPartialInst_x3f_86_);
v___y_91_ = v_val_98_;
goto v___jp_90_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Lean_mkApp3(v___x_89_, v_type_83_, v_leInst_85_, v___y_91_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_92_);
v___x_94_ = v___x_81_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
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
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec(v_declName_65_);
v_a_100_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_78_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_78_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___boxed(lean_object* v_declName_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v_declName_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec(v_a_110_);
lean_dec(v_a_109_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(lean_object* v_declName_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_Order_getStruct(v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_163_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_163_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_163_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_163_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_type_140_; lean_object* v_u_141_; lean_object* v_leInst_142_; lean_object* v_ltInst_x3f_143_; lean_object* v_lawfulOrderLTInst_x3f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_156_; 
v_type_140_ = lean_ctor_get(v_a_136_, 1);
lean_inc_ref(v_type_140_);
v_u_141_ = lean_ctor_get(v_a_136_, 2);
lean_inc(v_u_141_);
v_leInst_142_ = lean_ctor_get(v_a_136_, 4);
lean_inc_ref(v_leInst_142_);
v_ltInst_x3f_143_ = lean_ctor_get(v_a_136_, 5);
lean_inc(v_ltInst_x3f_143_);
v_lawfulOrderLTInst_x3f_144_ = lean_ctor_get(v_a_136_, 8);
lean_inc(v_lawfulOrderLTInst_x3f_144_);
lean_dec(v_a_136_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v_u_141_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = l_Lean_mkConst(v_declName_122_, v___x_146_);
if (lean_obj_tag(v_ltInst_x3f_143_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_161_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_160_);
v___y_156_ = v___x_161_;
goto v___jp_155_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v_ltInst_x3f_143_, 0);
lean_inc(v_val_162_);
lean_dec_ref(v_ltInst_x3f_143_);
v___y_156_ = v_val_162_;
goto v___jp_155_;
}
v___jp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = l_Lean_mkApp4(v___x_147_, v_type_140_, v_leInst_142_, v___y_149_, v___y_150_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_151_);
v___x_153_ = v___x_138_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
v___jp_155_:
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_144_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_158_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_157_);
v___y_149_ = v___y_156_;
v___y_150_ = v___x_158_;
goto v___jp_148_;
}
else
{
lean_object* v_val_159_; 
v_val_159_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_144_, 0);
lean_inc(v_val_159_);
lean_dec_ref(v_lawfulOrderLTInst_x3f_144_);
v___y_149_ = v___y_156_;
v___y_150_ = v_val_159_;
goto v___jp_148_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_declName_122_);
v_a_164_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_135_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_135_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix___boxed(lean_object* v_declName_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec(v_a_174_);
lean_dec(v_a_173_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(lean_object* v_declName_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_Grind_Order_getStruct(v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_201_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v___x_199_);
v___x_201_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_211_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_211_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_isPreorderInst_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v_isPreorderInst_206_ = lean_ctor_get(v_a_200_, 3);
lean_inc_ref(v_isPreorderInst_206_);
lean_dec(v_a_200_);
v___x_207_ = l_Lean_Expr_app___override(v_a_202_, v_isPreorderInst_206_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_209_ = v___x_204_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_dec(v_a_200_);
return v___x_201_;
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_declName_186_);
v_a_212_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_199_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_199_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix___boxed(lean_object* v_declName_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(lean_object* v_declName_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Grind_Order_getStruct(v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_247_);
v___x_249_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_264_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_264_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___y_255_; lean_object* v_isLinearPreInst_x3f_260_; 
v_isLinearPreInst_x3f_260_ = lean_ctor_get(v_a_248_, 7);
lean_inc(v_isLinearPreInst_x3f_260_);
lean_dec(v_a_248_);
if (lean_obj_tag(v_isLinearPreInst_x3f_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_262_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_261_);
v___y_255_ = v___x_262_;
goto v___jp_254_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v_isLinearPreInst_x3f_260_, 0);
lean_inc(v_val_263_);
lean_dec_ref(v_isLinearPreInst_x3f_260_);
v___y_255_ = v_val_263_;
goto v___jp_254_;
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = l_Lean_Expr_app___override(v_a_250_, v___y_255_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_256_);
v___x_258_ = v___x_252_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_dec(v_a_248_);
return v___x_249_;
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_declName_234_);
v_a_265_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_247_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_247_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix___boxed(lean_object* v_declName_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v_declName_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec(v_a_275_);
lean_dec(v_a_274_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix(lean_object* v_declName_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Meta_Grind_Order_getStruct(v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_321_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_321_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_321_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_321_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_type_305_; lean_object* v_u_306_; lean_object* v_leInst_307_; lean_object* v_isLinearPreInst_x3f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___y_313_; 
v_type_305_ = lean_ctor_get(v_a_301_, 1);
lean_inc_ref(v_type_305_);
v_u_306_ = lean_ctor_get(v_a_301_, 2);
lean_inc(v_u_306_);
v_leInst_307_ = lean_ctor_get(v_a_301_, 4);
lean_inc_ref(v_leInst_307_);
v_isLinearPreInst_x3f_308_ = lean_ctor_get(v_a_301_, 7);
lean_inc(v_isLinearPreInst_x3f_308_);
lean_dec(v_a_301_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v_u_306_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = l_Lean_mkConst(v_declName_287_, v___x_310_);
if (lean_obj_tag(v_isLinearPreInst_x3f_308_) == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_319_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_318_);
v___y_313_ = v___x_319_;
goto v___jp_312_;
}
else
{
lean_object* v_val_320_; 
v_val_320_ = lean_ctor_get(v_isLinearPreInst_x3f_308_, 0);
lean_inc(v_val_320_);
lean_dec_ref(v_isLinearPreInst_x3f_308_);
v___y_313_ = v_val_320_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_mkApp3(v___x_311_, v_type_305_, v_leInst_307_, v___y_313_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_314_);
v___x_316_ = v___x_303_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_declName_287_);
v_a_322_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_300_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_300_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix___boxed(lean_object* v_declName_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v_declName_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec(v_a_332_);
lean_dec(v_a_331_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object* v_declName_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Grind_Order_getStruct(v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v___x_359_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_381_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_381_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_381_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_381_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v_ringInst_x3f_371_; lean_object* v_orderedRingInst_x3f_372_; lean_object* v___y_374_; 
v_ringInst_x3f_371_ = lean_ctor_get(v_a_358_, 10);
lean_inc(v_ringInst_x3f_371_);
v_orderedRingInst_x3f_372_ = lean_ctor_get(v_a_358_, 11);
lean_inc(v_orderedRingInst_x3f_372_);
lean_dec(v_a_358_);
if (lean_obj_tag(v_ringInst_x3f_371_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_379_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_378_);
v___y_374_ = v___x_379_;
goto v___jp_373_;
}
else
{
lean_object* v_val_380_; 
v_val_380_ = lean_ctor_get(v_ringInst_x3f_371_, 0);
lean_inc(v_val_380_);
lean_dec_ref(v_ringInst_x3f_371_);
v___y_374_ = v_val_380_;
goto v___jp_373_;
}
v___jp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = l_Lean_mkAppB(v_a_360_, v___y_365_, v___y_366_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_367_);
v___x_369_ = v___x_362_;
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
v___jp_373_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_372_) == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_376_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_375_);
v___y_365_ = v___y_374_;
v___y_366_ = v___x_376_;
goto v___jp_364_;
}
else
{
lean_object* v_val_377_; 
v_val_377_ = lean_ctor_get(v_orderedRingInst_x3f_372_, 0);
lean_inc(v_val_377_);
lean_dec_ref(v_orderedRingInst_x3f_372_);
v___y_365_ = v___y_374_;
v___y_366_ = v_val_377_;
goto v___jp_364_;
}
}
}
}
else
{
lean_dec(v_a_358_);
return v___x_359_;
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_declName_344_);
v_a_382_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_357_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_357_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix___boxed(lean_object* v_declName_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v_declName_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec(v_a_392_);
lean_dec(v_a_391_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(lean_object* v_declName_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Grind_Order_getStruct(v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref(v___x_417_);
v___x_419_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v_declName_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_441_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_441_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_441_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_441_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v_ringInst_x3f_431_; lean_object* v_orderedRingInst_x3f_432_; lean_object* v___y_434_; 
v_ringInst_x3f_431_ = lean_ctor_get(v_a_418_, 10);
lean_inc(v_ringInst_x3f_431_);
v_orderedRingInst_x3f_432_ = lean_ctor_get(v_a_418_, 11);
lean_inc(v_orderedRingInst_x3f_432_);
lean_dec(v_a_418_);
if (lean_obj_tag(v_ringInst_x3f_431_) == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_439_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_438_);
v___y_434_ = v___x_439_;
goto v___jp_433_;
}
else
{
lean_object* v_val_440_; 
v_val_440_ = lean_ctor_get(v_ringInst_x3f_431_, 0);
lean_inc(v_val_440_);
lean_dec_ref(v_ringInst_x3f_431_);
v___y_434_ = v_val_440_;
goto v___jp_433_;
}
v___jp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Lean_mkAppB(v_a_420_, v___y_425_, v___y_426_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_427_);
v___x_429_ = v___x_422_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
v___jp_433_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_432_) == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_436_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_435_);
v___y_425_ = v___y_434_;
v___y_426_ = v___x_436_;
goto v___jp_424_;
}
else
{
lean_object* v_val_437_; 
v_val_437_ = lean_ctor_get(v_orderedRingInst_x3f_432_, 0);
lean_inc(v_val_437_);
lean_dec_ref(v_orderedRingInst_x3f_432_);
v___y_425_ = v___y_434_;
v___y_426_ = v_val_437_;
goto v___jp_424_;
}
}
}
}
else
{
lean_dec(v_a_418_);
return v___x_419_;
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_declName_404_);
v_a_442_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_417_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_417_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix___boxed(lean_object* v_declName_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v_declName_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(lean_object* v_u_491_, lean_object* v_v_492_, lean_object* v_w_493_, uint8_t v_strict_u2081_494_, uint8_t v_strict_u2082_495_, lean_object* v_h_u2081_496_, lean_object* v_h_u2082_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_h_511_; 
if (v_strict_u2081_494_ == 0)
{
if (v_strict_u2082_495_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4));
v___x_515_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_514_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
v_h_511_ = v_a_516_;
goto v___jp_510_;
}
else
{
lean_dec_ref(v_h_u2082_497_);
lean_dec_ref(v_h_u2081_496_);
lean_dec_ref(v_w_493_);
lean_dec_ref(v_v_492_);
lean_dec_ref(v_u_491_);
return v___x_515_;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6));
v___x_518_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_517_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref(v___x_518_);
v_h_511_ = v_a_519_;
goto v___jp_510_;
}
else
{
lean_dec_ref(v_h_u2082_497_);
lean_dec_ref(v_h_u2081_496_);
lean_dec_ref(v_w_493_);
lean_dec_ref(v_v_492_);
lean_dec_ref(v_u_491_);
return v___x_518_;
}
}
}
else
{
if (v_strict_u2082_495_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8));
v___x_521_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_520_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v_h_511_ = v_a_522_;
goto v___jp_510_;
}
else
{
lean_dec_ref(v_h_u2082_497_);
lean_dec_ref(v_h_u2081_496_);
lean_dec_ref(v_w_493_);
lean_dec_ref(v_v_492_);
lean_dec_ref(v_u_491_);
return v___x_521_;
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10));
v___x_524_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_523_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
v_h_511_ = v_a_525_;
goto v___jp_510_;
}
else
{
lean_dec_ref(v_h_u2082_497_);
lean_dec_ref(v_h_u2081_496_);
lean_dec_ref(v_w_493_);
lean_dec_ref(v_v_492_);
lean_dec_ref(v_u_491_);
return v___x_524_;
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = l_Lean_mkApp5(v_h_511_, v_u_491_, v_v_492_, v_w_493_, v_h_u2081_496_, v_h_u2082_497_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(lean_object** _args){
lean_object* v_u_526_ = _args[0];
lean_object* v_v_527_ = _args[1];
lean_object* v_w_528_ = _args[2];
lean_object* v_strict_u2081_529_ = _args[3];
lean_object* v_strict_u2082_530_ = _args[4];
lean_object* v_h_u2081_531_ = _args[5];
lean_object* v_h_u2082_532_ = _args[6];
lean_object* v_a_533_ = _args[7];
lean_object* v_a_534_ = _args[8];
lean_object* v_a_535_ = _args[9];
lean_object* v_a_536_ = _args[10];
lean_object* v_a_537_ = _args[11];
lean_object* v_a_538_ = _args[12];
lean_object* v_a_539_ = _args[13];
lean_object* v_a_540_ = _args[14];
lean_object* v_a_541_ = _args[15];
lean_object* v_a_542_ = _args[16];
lean_object* v_a_543_ = _args[17];
lean_object* v_a_544_ = _args[18];
_start:
{
uint8_t v_strict_u2081_boxed_545_; uint8_t v_strict_u2082_boxed_546_; lean_object* v_res_547_; 
v_strict_u2081_boxed_545_ = lean_unbox(v_strict_u2081_529_);
v_strict_u2082_boxed_546_ = lean_unbox(v_strict_u2082_530_);
v_res_547_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_526_, v_v_527_, v_w_528_, v_strict_u2081_boxed_545_, v_strict_u2082_boxed_546_, v_h_u2081_531_, v_h_u2082_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec(v_a_534_);
lean_dec(v_a_533_);
return v_res_547_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(lean_object* v_xs_548_, lean_object* v_i_549_){
_start:
{
lean_object* v_size_550_; uint8_t v___x_551_; 
v_size_550_ = lean_ctor_get(v_xs_548_, 2);
v___x_551_ = lean_nat_dec_lt(v_i_549_, v_size_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(lean_object* v_xs_552_, lean_object* v_i_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_xs_552_, v_i_553_);
lean_dec(v_i_553_);
lean_dec_ref(v_xs_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_to_int(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(lean_object* v_p_u2081_558_, lean_object* v_p_u2082_559_, lean_object* v_v_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_w_573_; lean_object* v_k_574_; lean_object* v_proof_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_634_; 
v_w_573_ = lean_ctor_get(v_p_u2081_558_, 0);
v_k_574_ = lean_ctor_get(v_p_u2081_558_, 1);
v_proof_575_ = lean_ctor_get(v_p_u2081_558_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_p_u2081_558_);
if (v_isSharedCheck_634_ == 0)
{
v___x_577_ = v_p_u2081_558_;
v_isShared_578_ = v_isSharedCheck_634_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_proof_575_);
lean_inc(v_k_574_);
lean_inc(v_w_573_);
lean_dec(v_p_u2081_558_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_634_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___y_580_; lean_object* v___y_581_; uint8_t v___y_582_; lean_object* v_k_588_; uint8_t v_strict_589_; lean_object* v_w_590_; lean_object* v_proof_591_; uint8_t v_strict_592_; lean_object* v___x_593_; 
v_k_588_ = lean_ctor_get(v_p_u2082_559_, 1);
lean_inc_ref(v_k_588_);
v_strict_589_ = lean_ctor_get_uint8(v_k_574_, sizeof(void*)*1);
lean_dec_ref(v_k_574_);
v_w_590_ = lean_ctor_get(v_p_u2082_559_, 0);
lean_inc(v_w_590_);
v_proof_591_ = lean_ctor_get(v_p_u2082_559_, 2);
lean_inc_ref(v_proof_591_);
lean_dec_ref(v_p_u2082_559_);
v_strict_592_ = lean_ctor_get_uint8(v_k_588_, sizeof(void*)*1);
lean_dec_ref(v_k_588_);
v___x_593_ = l_Lean_Meta_Grind_Order_getStruct(v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v_nodes_610_; lean_object* v___x_611_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_619_; uint8_t v___x_623_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v___x_593_);
v_nodes_610_ = lean_ctor_get(v_a_594_, 14);
lean_inc_ref(v_nodes_610_);
lean_dec(v_a_594_);
v___x_611_ = l_Lean_instInhabitedExpr;
v___x_623_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_610_, v_w_573_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = l_outOfBounds___redArg(v___x_611_);
v___y_619_ = v___x_624_;
goto v___jp_618_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentArray_get_x21___redArg(v___x_611_, v_nodes_610_, v_w_573_);
v___y_619_ = v___x_625_;
goto v___jp_618_;
}
v___jp_595_:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v___y_597_, v___y_596_, v___y_598_, v_strict_589_, v_strict_592_, v_proof_575_, v_proof_591_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
if (v_strict_589_ == 0)
{
v___y_580_ = v___x_601_;
v___y_581_ = v_a_600_;
v___y_582_ = v_strict_592_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___x_601_;
v___y_581_ = v_a_600_;
v___y_582_ = v_strict_589_;
goto v___jp_579_;
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_del_object(v___x_577_);
lean_dec(v_w_573_);
v_a_602_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_599_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_599_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
v___jp_612_:
{
uint8_t v___x_615_; 
v___x_615_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_610_, v_v_560_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_nodes_610_);
v___x_616_ = l_outOfBounds___redArg(v___x_611_);
v___y_596_ = v___y_614_;
v___y_597_ = v___y_613_;
v___y_598_ = v___x_616_;
goto v___jp_595_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_PersistentArray_get_x21___redArg(v___x_611_, v_nodes_610_, v_v_560_);
lean_dec_ref(v_nodes_610_);
v___y_596_ = v___y_614_;
v___y_597_ = v___y_613_;
v___y_598_ = v___x_617_;
goto v___jp_595_;
}
}
v___jp_618_:
{
uint8_t v___x_620_; 
v___x_620_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_610_, v_w_590_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_w_590_);
v___x_621_ = l_outOfBounds___redArg(v___x_611_);
v___y_613_ = v___y_619_;
v___y_614_ = v___x_621_;
goto v___jp_612_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentArray_get_x21___redArg(v___x_611_, v_nodes_610_, v_w_590_);
lean_dec(v_w_590_);
v___y_613_ = v___y_619_;
v___y_614_ = v___x_622_;
goto v___jp_612_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_proof_591_);
lean_dec(v_w_590_);
lean_del_object(v___x_577_);
lean_dec_ref(v_proof_575_);
lean_dec(v_w_573_);
v_a_626_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_593_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_593_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
v___jp_579_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_inc(v___y_580_);
v___x_583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_583_, 0, v___y_580_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___y_582_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 2, v___y_581_);
lean_ctor_set(v___x_577_, 1, v___x_583_);
v___x_585_ = v___x_577_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_w_573_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___y_581_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(lean_object* v_p_u2081_635_, lean_object* v_p_u2082_636_, lean_object* v_v_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_635_, v_p_u2082_636_, v_v_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_v_637_);
return v_res_650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_Level_ofNat(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4);
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2));
v___x_663_ = l_Lean_Expr_const___override(v___x_662_, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7));
v___x_669_ = l_Lean_Expr_const___override(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_box(0);
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10));
v___x_676_ = l_Lean_Expr_const___override(v___x_675_, v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(lean_object* v_u_701_, lean_object* v_v_702_, lean_object* v_w_703_, lean_object* v_k_u2081_704_, lean_object* v_k_u2082_705_, lean_object* v_h_u2081_706_, lean_object* v_h_u2082_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v_k_761_; uint8_t v_strict_762_; lean_object* v_h_764_; 
v_k_761_ = lean_ctor_get(v_k_u2081_704_, 0);
v_strict_762_ = lean_ctor_get_uint8(v_k_u2081_704_, sizeof(void*)*1);
if (v_strict_762_ == 0)
{
uint8_t v_strict_778_; 
v_strict_778_ = lean_ctor_get_uint8(v_k_u2082_705_, sizeof(void*)*1);
if (v_strict_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13));
v___x_780_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_779_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v_h_764_ = v_a_781_;
goto v___jp_763_;
}
else
{
lean_dec_ref(v_h_u2082_707_);
lean_dec_ref(v_h_u2081_706_);
lean_dec_ref(v_w_703_);
lean_dec_ref(v_v_702_);
lean_dec_ref(v_u_701_);
return v___x_780_;
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15));
v___x_783_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_782_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v_h_764_ = v_a_784_;
goto v___jp_763_;
}
else
{
lean_dec_ref(v_h_u2082_707_);
lean_dec_ref(v_h_u2081_706_);
lean_dec_ref(v_w_703_);
lean_dec_ref(v_v_702_);
lean_dec_ref(v_u_701_);
return v___x_783_;
}
}
}
else
{
uint8_t v_strict_785_; 
v_strict_785_ = lean_ctor_get_uint8(v_k_u2082_705_, sizeof(void*)*1);
if (v_strict_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17));
v___x_787_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_786_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
v_h_764_ = v_a_788_;
goto v___jp_763_;
}
else
{
lean_dec_ref(v_h_u2082_707_);
lean_dec_ref(v_h_u2081_706_);
lean_dec_ref(v_w_703_);
lean_dec_ref(v_v_702_);
lean_dec_ref(v_u_701_);
return v___x_787_;
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19));
v___x_790_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_789_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref(v___x_790_);
v_h_764_ = v_a_791_;
goto v___jp_763_;
}
else
{
lean_dec_ref(v_h_u2082_707_);
lean_dec_ref(v_h_u2081_706_);
lean_dec_ref(v_w_703_);
lean_dec_ref(v_v_702_);
lean_dec_ref(v_u_701_);
return v___x_790_;
}
}
}
v___jp_720_:
{
lean_object* v_h_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_h_725_ = l_Lean_mkApp6(v___y_721_, v_u_701_, v_v_702_, v_w_703_, v___y_723_, v___y_722_, v___y_724_);
v___x_726_ = l_Lean_eagerReflBoolTrue;
v___x_727_ = l_Lean_mkApp3(v_h_725_, v_h_u2081_706_, v_h_u2082_707_, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
v___jp_729_:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_735_ = lean_int_dec_le(v___x_734_, v___y_731_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_739_ = lean_int_neg(v___y_731_);
lean_dec(v___y_731_);
v___x_740_ = l_Int_toNat(v___x_739_);
lean_dec(v___x_739_);
v___x_741_ = l_Lean_instToExprInt_mkNat(v___x_740_);
v___x_742_ = l_Lean_mkApp3(v___x_736_, v___x_737_, v___x_738_, v___x_741_);
v___y_721_ = v___y_730_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_732_;
v___y_724_ = v___x_742_;
goto v___jp_720_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Int_toNat(v___y_731_);
lean_dec(v___y_731_);
v___x_744_ = l_Lean_instToExprInt_mkNat(v___x_743_);
v___y_721_ = v___y_730_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_732_;
v___y_724_ = v___x_744_;
goto v___jp_720_;
}
}
v___jp_745_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_751_ = lean_int_dec_le(v___x_750_, v___y_748_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_755_ = lean_int_neg(v___y_748_);
v___x_756_ = l_Int_toNat(v___x_755_);
lean_dec(v___x_755_);
v___x_757_ = l_Lean_instToExprInt_mkNat(v___x_756_);
v___x_758_ = l_Lean_mkApp3(v___x_752_, v___x_753_, v___x_754_, v___x_757_);
v___y_730_ = v___y_746_;
v___y_731_ = v___y_747_;
v___y_732_ = v___y_749_;
v___y_733_ = v___x_758_;
goto v___jp_729_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Int_toNat(v___y_748_);
v___x_760_ = l_Lean_instToExprInt_mkNat(v___x_759_);
v___y_730_ = v___y_746_;
v___y_731_ = v___y_747_;
v___y_732_ = v___y_749_;
v___y_733_ = v___x_760_;
goto v___jp_729_;
}
}
v___jp_763_:
{
lean_object* v_k_765_; lean_object* v_k_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_k_765_ = lean_ctor_get(v_k_u2082_705_, 0);
v_k_766_ = lean_int_add(v_k_761_, v_k_765_);
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_768_ = lean_int_dec_le(v___x_767_, v_k_761_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_772_ = lean_int_neg(v_k_761_);
v___x_773_ = l_Int_toNat(v___x_772_);
lean_dec(v___x_772_);
v___x_774_ = l_Lean_instToExprInt_mkNat(v___x_773_);
v___x_775_ = l_Lean_mkApp3(v___x_769_, v___x_770_, v___x_771_, v___x_774_);
v___y_746_ = v_h_764_;
v___y_747_ = v_k_766_;
v___y_748_ = v_k_765_;
v___y_749_ = v___x_775_;
goto v___jp_745_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Int_toNat(v_k_761_);
v___x_777_ = l_Lean_instToExprInt_mkNat(v___x_776_);
v___y_746_ = v_h_764_;
v___y_747_ = v_k_766_;
v___y_748_ = v_k_765_;
v___y_749_ = v___x_777_;
goto v___jp_745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(lean_object** _args){
lean_object* v_u_792_ = _args[0];
lean_object* v_v_793_ = _args[1];
lean_object* v_w_794_ = _args[2];
lean_object* v_k_u2081_795_ = _args[3];
lean_object* v_k_u2082_796_ = _args[4];
lean_object* v_h_u2081_797_ = _args[5];
lean_object* v_h_u2082_798_ = _args[6];
lean_object* v_a_799_ = _args[7];
lean_object* v_a_800_ = _args[8];
lean_object* v_a_801_ = _args[9];
lean_object* v_a_802_ = _args[10];
lean_object* v_a_803_ = _args[11];
lean_object* v_a_804_ = _args[12];
lean_object* v_a_805_ = _args[13];
lean_object* v_a_806_ = _args[14];
lean_object* v_a_807_ = _args[15];
lean_object* v_a_808_ = _args[16];
lean_object* v_a_809_ = _args[17];
lean_object* v_a_810_ = _args[18];
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_792_, v_v_793_, v_w_794_, v_k_u2081_795_, v_k_u2082_796_, v_h_u2081_797_, v_h_u2082_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_k_u2082_796_);
lean_dec_ref(v_k_u2081_795_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(lean_object* v_p_u2081_812_, lean_object* v_p_u2082_813_, lean_object* v_v_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_w_827_; lean_object* v_k_828_; lean_object* v_proof_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_890_; 
v_w_827_ = lean_ctor_get(v_p_u2081_812_, 0);
v_k_828_ = lean_ctor_get(v_p_u2081_812_, 1);
v_proof_829_ = lean_ctor_get(v_p_u2081_812_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_p_u2081_812_);
if (v_isSharedCheck_890_ == 0)
{
v___x_831_ = v_p_u2081_812_;
v_isShared_832_ = v_isSharedCheck_890_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_proof_829_);
lean_inc(v_k_828_);
lean_inc(v_w_827_);
lean_dec(v_p_u2081_812_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_890_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___y_834_; lean_object* v___y_835_; uint8_t v___y_836_; lean_object* v_w_842_; lean_object* v_k_843_; lean_object* v_proof_844_; lean_object* v___x_845_; 
v_w_842_ = lean_ctor_get(v_p_u2082_813_, 0);
lean_inc(v_w_842_);
v_k_843_ = lean_ctor_get(v_p_u2082_813_, 1);
lean_inc_ref(v_k_843_);
v_proof_844_ = lean_ctor_get(v_p_u2082_813_, 2);
lean_inc_ref(v_proof_844_);
lean_dec_ref(v_p_u2082_813_);
v___x_845_ = l_Lean_Meta_Grind_Order_getStruct(v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v_nodes_866_; lean_object* v___x_867_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_875_; uint8_t v___x_879_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v_nodes_866_ = lean_ctor_get(v_a_846_, 14);
lean_inc_ref(v_nodes_866_);
lean_dec(v_a_846_);
v___x_867_ = l_Lean_instInhabitedExpr;
v___x_879_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_866_, v_w_827_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = l_outOfBounds___redArg(v___x_867_);
v___y_875_ = v___x_880_;
goto v___jp_874_;
}
else
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentArray_get_x21___redArg(v___x_867_, v_nodes_866_, v_w_827_);
v___y_875_ = v___x_881_;
goto v___jp_874_;
}
v___jp_847_:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v___y_848_, v___y_849_, v___y_850_, v_k_828_, v_k_843_, v_proof_829_, v_proof_844_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v_k_853_; uint8_t v_strict_854_; lean_object* v_k_855_; uint8_t v_strict_856_; lean_object* v___x_857_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_851_);
v_k_853_ = lean_ctor_get(v_k_828_, 0);
lean_inc(v_k_853_);
v_strict_854_ = lean_ctor_get_uint8(v_k_828_, sizeof(void*)*1);
lean_dec_ref(v_k_828_);
v_k_855_ = lean_ctor_get(v_k_843_, 0);
lean_inc(v_k_855_);
v_strict_856_ = lean_ctor_get_uint8(v_k_843_, sizeof(void*)*1);
lean_dec_ref(v_k_843_);
v___x_857_ = lean_int_add(v_k_853_, v_k_855_);
lean_dec(v_k_855_);
lean_dec(v_k_853_);
if (v_strict_854_ == 0)
{
v___y_834_ = v___x_857_;
v___y_835_ = v_a_852_;
v___y_836_ = v_strict_856_;
goto v___jp_833_;
}
else
{
v___y_834_ = v___x_857_;
v___y_835_ = v_a_852_;
v___y_836_ = v_strict_854_;
goto v___jp_833_;
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v_k_843_);
lean_del_object(v___x_831_);
lean_dec_ref(v_k_828_);
lean_dec(v_w_827_);
v_a_858_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_851_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_851_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
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
v___jp_868_:
{
uint8_t v___x_871_; 
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_866_, v_v_814_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref(v_nodes_866_);
v___x_872_ = l_outOfBounds___redArg(v___x_867_);
v___y_848_ = v___y_869_;
v___y_849_ = v___y_870_;
v___y_850_ = v___x_872_;
goto v___jp_847_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentArray_get_x21___redArg(v___x_867_, v_nodes_866_, v_v_814_);
lean_dec_ref(v_nodes_866_);
v___y_848_ = v___y_869_;
v___y_849_ = v___y_870_;
v___y_850_ = v___x_873_;
goto v___jp_847_;
}
}
v___jp_874_:
{
uint8_t v___x_876_; 
v___x_876_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_866_, v_w_842_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v_w_842_);
v___x_877_ = l_outOfBounds___redArg(v___x_867_);
v___y_869_ = v___y_875_;
v___y_870_ = v___x_877_;
goto v___jp_868_;
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentArray_get_x21___redArg(v___x_867_, v_nodes_866_, v_w_842_);
lean_dec(v_w_842_);
v___y_869_ = v___y_875_;
v___y_870_ = v___x_878_;
goto v___jp_868_;
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_proof_844_);
lean_dec_ref(v_k_843_);
lean_dec(v_w_842_);
lean_del_object(v___x_831_);
lean_dec_ref(v_proof_829_);
lean_dec_ref(v_k_828_);
lean_dec(v_w_827_);
v_a_882_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_845_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_845_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
v___jp_833_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_837_, 0, v___y_834_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*1, v___y_836_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 2, v___y_835_);
lean_ctor_set(v___x_831_, 1, v___x_837_);
v___x_839_ = v___x_831_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_w_827_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v___y_835_);
v___x_839_ = v_reuseFailAlloc_841_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(lean_object* v_p_u2081_891_, lean_object* v_p_u2082_892_, lean_object* v_v_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_891_, v_p_u2082_892_, v_v_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec(v_v_893_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object* v_p_u2081_907_, lean_object* v_p_u2082_908_, lean_object* v_v_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Meta_Grind_Order_isRing(v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; uint8_t v___x_924_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
v___x_924_ = lean_unbox(v_a_923_);
lean_dec(v_a_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_907_, v_p_u2082_908_, v_v_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; 
v___x_926_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_907_, v_p_u2082_908_, v_v_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
return v___x_926_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_p_u2082_908_);
lean_dec_ref(v_p_u2081_907_);
v_a_927_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_922_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_922_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans___boxed(lean_object* v_p_u2081_935_, lean_object* v_p_u2082_936_, lean_object* v_v_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_Grind_Order_mkTrans(v_p_u2081_935_, v_p_u2082_936_, v_v_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_v_937_);
return v_res_950_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___x_1910__overap_967_; lean_object* v___x_968_; 
v___x_965_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0);
v___f_966_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_966_, 0, v___x_965_);
v___x_1910__overap_967_ = lean_panic_fn_borrowed(v___f_966_, v_msg_952_);
lean_dec_ref(v___f_966_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v___y_955_);
lean_inc(v___y_954_);
lean_inc(v___y_953_);
v___x_968_ = lean_apply_12(v___x_1910__overap_967_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, lean_box(0));
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec(v___y_971_);
lean_dec(v___y_970_);
return v_res_982_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2));
v___x_987_ = lean_unsigned_to_nat(4u);
v___x_988_ = lean_unsigned_to_nat(133u);
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1));
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_991_ = l_mkPanicMessageWithDecl(v___x_990_, v___x_989_, v___x_988_, v___x_987_, v___x_986_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(lean_object* v_u_998_, lean_object* v_v_999_, lean_object* v_k_1000_, lean_object* v_huv_1001_, lean_object* v_k_x27_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
uint8_t v_strict_1018_; uint8_t v_strict_1019_; 
v_strict_1018_ = lean_ctor_get_uint8(v_k_1000_, sizeof(void*)*1);
v_strict_1019_ = lean_ctor_get_uint8(v_k_x27_1002_, sizeof(void*)*1);
if (v_strict_1018_ == 0)
{
if (v_strict_1019_ == 0)
{
lean_object* v___x_1032_; 
lean_dec_ref(v_v_999_);
lean_dec_ref(v_u_998_);
v___x_1032_ = l_Lean_Meta_mkEqTrue(v_huv_1001_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1032_;
}
else
{
goto v___jp_1020_;
}
}
else
{
if (v_strict_1019_ == 0)
{
goto v___jp_1020_;
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v_v_999_);
lean_dec_ref(v_u_998_);
v___x_1033_ = l_Lean_Meta_mkEqTrue(v_huv_1001_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1033_;
}
}
v___jp_1015_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3);
v___x_1017_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1016_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1017_;
}
v___jp_1020_:
{
if (v_strict_1018_ == 0)
{
lean_dec_ref(v_huv_1001_);
lean_dec_ref(v_v_999_);
lean_dec_ref(v_u_998_);
goto v___jp_1015_;
}
else
{
if (v_strict_1019_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5));
v___x_1022_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_1021_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = l_Lean_mkApp3(v_a_1023_, v_u_998_, v_v_999_, v_huv_1001_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_dec_ref(v_huv_1001_);
lean_dec_ref(v_v_999_);
lean_dec_ref(v_u_998_);
return v___x_1022_;
}
}
else
{
lean_dec_ref(v_huv_1001_);
lean_dec_ref(v_v_999_);
lean_dec_ref(v_u_998_);
goto v___jp_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___boxed(lean_object** _args){
lean_object* v_u_1034_ = _args[0];
lean_object* v_v_1035_ = _args[1];
lean_object* v_k_1036_ = _args[2];
lean_object* v_huv_1037_ = _args[3];
lean_object* v_k_x27_1038_ = _args[4];
lean_object* v_a_1039_ = _args[5];
lean_object* v_a_1040_ = _args[6];
lean_object* v_a_1041_ = _args[7];
lean_object* v_a_1042_ = _args[8];
lean_object* v_a_1043_ = _args[9];
lean_object* v_a_1044_ = _args[10];
lean_object* v_a_1045_ = _args[11];
lean_object* v_a_1046_ = _args[12];
lean_object* v_a_1047_ = _args[13];
lean_object* v_a_1048_ = _args[14];
lean_object* v_a_1049_ = _args[15];
lean_object* v_a_1050_ = _args[16];
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1034_, v_v_1035_, v_k_1036_, v_huv_1037_, v_k_x27_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_k_x27_1038_);
lean_dec_ref(v_k_1036_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(lean_object* v_u_1076_, lean_object* v_v_1077_, lean_object* v_k_1078_, lean_object* v_huv_1079_, lean_object* v_k_x27_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_k_1100_; uint8_t v_strict_1101_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1117_; 
v_k_1100_ = lean_ctor_get(v_k_x27_1080_, 0);
v_strict_1101_ = lean_ctor_get_uint8(v_k_x27_1080_, sizeof(void*)*1);
if (v_strict_1101_ == 0)
{
uint8_t v_strict_1132_; 
v_strict_1132_ = lean_ctor_get_uint8(v_k_1078_, sizeof(void*)*1);
if (v_strict_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1));
v___y_1117_ = v___x_1133_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3));
v___y_1117_ = v___x_1134_;
goto v___jp_1116_;
}
}
else
{
uint8_t v_strict_1135_; 
v_strict_1135_ = lean_ctor_get_uint8(v_k_1078_, sizeof(void*)*1);
if (v_strict_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5));
v___y_1117_ = v___x_1136_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7));
v___y_1117_ = v___x_1137_;
goto v___jp_1116_;
}
}
v___jp_1093_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = l_Lean_eagerReflBoolTrue;
v___x_1098_ = l_Lean_mkApp6(v___y_1094_, v_u_1076_, v_v_1077_, v___y_1095_, v___y_1096_, v___x_1097_, v_huv_1079_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
v___jp_1102_:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1106_ = lean_int_dec_le(v___x_1105_, v_k_1100_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1110_ = lean_int_neg(v_k_1100_);
v___x_1111_ = l_Int_toNat(v___x_1110_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_instToExprInt_mkNat(v___x_1111_);
v___x_1113_ = l_Lean_mkApp3(v___x_1107_, v___x_1108_, v___x_1109_, v___x_1112_);
v___y_1094_ = v___y_1103_;
v___y_1095_ = v___y_1104_;
v___y_1096_ = v___x_1113_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = l_Int_toNat(v_k_1100_);
v___x_1115_ = l_Lean_instToExprInt_mkNat(v___x_1114_);
v___y_1094_ = v___y_1103_;
v___y_1095_ = v___y_1104_;
v___y_1096_ = v___x_1115_;
goto v___jp_1093_;
}
}
v___jp_1116_:
{
lean_object* v___x_1118_; 
lean_inc(v___y_1117_);
v___x_1118_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1117_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_k_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v_k_1120_ = lean_ctor_get(v_k_1078_, 0);
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1122_ = lean_int_dec_le(v___x_1121_, v_k_1120_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1126_ = lean_int_neg(v_k_1120_);
v___x_1127_ = l_Int_toNat(v___x_1126_);
lean_dec(v___x_1126_);
v___x_1128_ = l_Lean_instToExprInt_mkNat(v___x_1127_);
v___x_1129_ = l_Lean_mkApp3(v___x_1123_, v___x_1124_, v___x_1125_, v___x_1128_);
v___y_1103_ = v_a_1119_;
v___y_1104_ = v___x_1129_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = l_Int_toNat(v_k_1120_);
v___x_1131_ = l_Lean_instToExprInt_mkNat(v___x_1130_);
v___y_1103_ = v_a_1119_;
v___y_1104_ = v___x_1131_;
goto v___jp_1102_;
}
}
else
{
lean_dec_ref(v_huv_1079_);
lean_dec_ref(v_v_1077_);
lean_dec_ref(v_u_1076_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(lean_object** _args){
lean_object* v_u_1138_ = _args[0];
lean_object* v_v_1139_ = _args[1];
lean_object* v_k_1140_ = _args[2];
lean_object* v_huv_1141_ = _args[3];
lean_object* v_k_x27_1142_ = _args[4];
lean_object* v_a_1143_ = _args[5];
lean_object* v_a_1144_ = _args[6];
lean_object* v_a_1145_ = _args[7];
lean_object* v_a_1146_ = _args[8];
lean_object* v_a_1147_ = _args[9];
lean_object* v_a_1148_ = _args[10];
lean_object* v_a_1149_ = _args[11];
lean_object* v_a_1150_ = _args[12];
lean_object* v_a_1151_ = _args[13];
lean_object* v_a_1152_ = _args[14];
lean_object* v_a_1153_ = _args[15];
lean_object* v_a_1154_ = _args[16];
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1138_, v_v_1139_, v_k_1140_, v_huv_1141_, v_k_x27_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_k_x27_1142_);
lean_dec_ref(v_k_1140_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object* v_u_1156_, lean_object* v_v_1157_, lean_object* v_k_1158_, lean_object* v_huv_1159_, lean_object* v_k_x27_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_Grind_Order_isRing(v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; uint8_t v___x_1175_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = lean_unbox(v_a_1174_);
lean_dec(v_a_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1156_, v_v_1157_, v_k_1158_, v_huv_1159_, v_k_x27_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1156_, v_v_1157_, v_k_1158_, v_huv_1159_, v_k_x27_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
return v___x_1177_;
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_huv_1159_);
lean_dec_ref(v_v_1157_);
lean_dec_ref(v_u_1156_);
v_a_1178_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1173_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1173_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof___boxed(lean_object** _args){
lean_object* v_u_1186_ = _args[0];
lean_object* v_v_1187_ = _args[1];
lean_object* v_k_1188_ = _args[2];
lean_object* v_huv_1189_ = _args[3];
lean_object* v_k_x27_1190_ = _args[4];
lean_object* v_a_1191_ = _args[5];
lean_object* v_a_1192_ = _args[6];
lean_object* v_a_1193_ = _args[7];
lean_object* v_a_1194_ = _args[8];
lean_object* v_a_1195_ = _args[9];
lean_object* v_a_1196_ = _args[10];
lean_object* v_a_1197_ = _args[11];
lean_object* v_a_1198_ = _args[12];
lean_object* v_a_1199_ = _args[13];
lean_object* v_a_1200_ = _args[14];
lean_object* v_a_1201_ = _args[15];
lean_object* v_a_1202_ = _args[16];
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_u_1186_, v_v_1187_, v_k_1188_, v_huv_1189_, v_k_x27_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_k_x27_1190_);
lean_dec_ref(v_k_1188_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(lean_object* v_u_1216_, lean_object* v_k_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v_k_1236_; uint8_t v_strict_1237_; lean_object* v___y_1239_; 
v_k_1236_ = lean_ctor_get(v_k_1217_, 0);
v_strict_1237_ = lean_ctor_get_uint8(v_k_1217_, sizeof(void*)*1);
if (v_strict_1237_ == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1));
v___y_1239_ = v___x_1253_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3));
v___y_1239_ = v___x_1254_;
goto v___jp_1238_;
}
v___jp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = l_Lean_eagerReflBoolTrue;
v___x_1234_ = l_Lean_mkApp3(v___y_1231_, v_u_1216_, v___y_1232_, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; 
lean_inc(v___y_1239_);
v___x_1240_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1239_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1243_ = lean_int_dec_le(v___x_1242_, v_k_1236_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1247_ = lean_int_neg(v_k_1236_);
v___x_1248_ = l_Int_toNat(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1249_ = l_Lean_instToExprInt_mkNat(v___x_1248_);
v___x_1250_ = l_Lean_mkApp3(v___x_1244_, v___x_1245_, v___x_1246_, v___x_1249_);
v___y_1231_ = v_a_1241_;
v___y_1232_ = v___x_1250_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Int_toNat(v_k_1236_);
v___x_1252_ = l_Lean_instToExprInt_mkNat(v___x_1251_);
v___y_1231_ = v_a_1241_;
v___y_1232_ = v___x_1252_;
goto v___jp_1230_;
}
}
else
{
lean_dec_ref(v_u_1216_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(lean_object* v_u_1255_, lean_object* v_k_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1255_, v_k_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_k_1256_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(lean_object* v_u_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1));
v___x_1290_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_1289_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = l_Lean_Expr_app___override(v_a_1291_, v_u_1276_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_dec_ref(v_u_1276_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___boxed(lean_object* v_u_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec(v_a_1301_);
return v_res_1313_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1));
v___x_1317_ = lean_unsigned_to_nat(4u);
v___x_1318_ = lean_unsigned_to_nat(175u);
v___x_1319_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0));
v___x_1320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1321_ = l_mkPanicMessageWithDecl(v___x_1320_, v___x_1319_, v___x_1318_, v___x_1317_, v___x_1316_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object* v_u_1322_, lean_object* v_k_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Meta_Grind_Order_isRing(v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; uint8_t v___x_1338_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = lean_unbox(v_a_1337_);
lean_dec(v_a_1337_);
if (v___x_1338_ == 0)
{
uint8_t v_strict_1339_; 
v_strict_1339_ = lean_ctor_get_uint8(v_k_1323_, sizeof(void*)*1);
if (v_strict_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1322_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_u_1322_);
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2);
v___x_1342_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1341_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1322_, v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1343_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_u_1322_);
v_a_1344_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1336_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1336_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___boxed(lean_object* v_u_1352_, lean_object* v_k_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_u_1352_, v_k_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_k_1353_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(lean_object* v_msg_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_panic_fn_borrowed(v___x_1368_, v_msg_1367_);
return v___x_1369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1));
v___x_1373_ = lean_unsigned_to_nat(22u);
v___x_1374_ = lean_unsigned_to_nat(183u);
v___x_1375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0));
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1377_ = l_mkPanicMessageWithDecl(v___x_1376_, v___x_1375_, v___x_1374_, v___x_1373_, v___x_1372_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(lean_object* v_u_1396_, lean_object* v_v_1397_, lean_object* v_k_1398_, lean_object* v_huv_1399_, lean_object* v_k_x27_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___y_1414_; uint8_t v_strict_1425_; 
v_strict_1425_ = lean_ctor_get_uint8(v_k_x27_1400_, sizeof(void*)*1);
if (v_strict_1425_ == 0)
{
uint8_t v_strict_1426_; 
v_strict_1426_ = lean_ctor_get_uint8(v_k_1398_, sizeof(void*)*1);
if (v_strict_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2);
v___x_1428_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_1427_);
v___y_1414_ = v___x_1428_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4));
v___y_1414_ = v___x_1429_;
goto v___jp_1413_;
}
}
else
{
uint8_t v_strict_1430_; 
v_strict_1430_ = lean_ctor_get_uint8(v_k_1398_, sizeof(void*)*1);
if (v_strict_1430_ == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6));
v___y_1414_ = v___x_1431_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8));
v___y_1414_ = v___x_1432_;
goto v___jp_1413_;
}
}
v___jp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___y_1414_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = l_Lean_mkApp3(v_a_1416_, v_u_1396_, v_v_1397_, v_huv_1399_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_dec_ref(v_huv_1399_);
lean_dec_ref(v_v_1397_);
lean_dec_ref(v_u_1396_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___boxed(lean_object** _args){
lean_object* v_u_1433_ = _args[0];
lean_object* v_v_1434_ = _args[1];
lean_object* v_k_1435_ = _args[2];
lean_object* v_huv_1436_ = _args[3];
lean_object* v_k_x27_1437_ = _args[4];
lean_object* v_a_1438_ = _args[5];
lean_object* v_a_1439_ = _args[6];
lean_object* v_a_1440_ = _args[7];
lean_object* v_a_1441_ = _args[8];
lean_object* v_a_1442_ = _args[9];
lean_object* v_a_1443_ = _args[10];
lean_object* v_a_1444_ = _args[11];
lean_object* v_a_1445_ = _args[12];
lean_object* v_a_1446_ = _args[13];
lean_object* v_a_1447_ = _args[14];
lean_object* v_a_1448_ = _args[15];
lean_object* v_a_1449_ = _args[16];
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1433_, v_v_1434_, v_k_1435_, v_huv_1436_, v_k_x27_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_k_x27_1437_);
lean_dec_ref(v_k_1435_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(lean_object* v_u_1475_, lean_object* v_v_1476_, lean_object* v_k_1477_, lean_object* v_huv_1478_, lean_object* v_k_x27_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v_k_1499_; uint8_t v_strict_1500_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1516_; 
v_k_1499_ = lean_ctor_get(v_k_x27_1479_, 0);
v_strict_1500_ = lean_ctor_get_uint8(v_k_x27_1479_, sizeof(void*)*1);
if (v_strict_1500_ == 0)
{
uint8_t v_strict_1531_; 
v_strict_1531_ = lean_ctor_get_uint8(v_k_1477_, sizeof(void*)*1);
if (v_strict_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1));
v___y_1516_ = v___x_1532_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3));
v___y_1516_ = v___x_1533_;
goto v___jp_1515_;
}
}
else
{
uint8_t v_strict_1534_; 
v_strict_1534_ = lean_ctor_get_uint8(v_k_1477_, sizeof(void*)*1);
if (v_strict_1534_ == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5));
v___y_1516_ = v___x_1535_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7));
v___y_1516_ = v___x_1536_;
goto v___jp_1515_;
}
}
v___jp_1492_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = l_Lean_eagerReflBoolTrue;
v___x_1497_ = l_Lean_mkApp6(v___y_1494_, v_u_1475_, v_v_1476_, v___y_1493_, v___y_1495_, v___x_1496_, v_huv_1478_);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
v___jp_1501_:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1505_ = lean_int_dec_le(v___x_1504_, v_k_1499_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1509_ = lean_int_neg(v_k_1499_);
v___x_1510_ = l_Int_toNat(v___x_1509_);
lean_dec(v___x_1509_);
v___x_1511_ = l_Lean_instToExprInt_mkNat(v___x_1510_);
v___x_1512_ = l_Lean_mkApp3(v___x_1506_, v___x_1507_, v___x_1508_, v___x_1511_);
v___y_1493_ = v___y_1503_;
v___y_1494_ = v___y_1502_;
v___y_1495_ = v___x_1512_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = l_Int_toNat(v_k_1499_);
v___x_1514_ = l_Lean_instToExprInt_mkNat(v___x_1513_);
v___y_1493_ = v___y_1503_;
v___y_1494_ = v___y_1502_;
v___y_1495_ = v___x_1514_;
goto v___jp_1492_;
}
}
v___jp_1515_:
{
lean_object* v___x_1517_; 
lean_inc(v___y_1516_);
v___x_1517_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1516_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v_k_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v_k_1519_ = lean_ctor_get(v_k_1477_, 0);
v___x_1520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1521_ = lean_int_dec_le(v___x_1520_, v_k_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1525_ = lean_int_neg(v_k_1519_);
v___x_1526_ = l_Int_toNat(v___x_1525_);
lean_dec(v___x_1525_);
v___x_1527_ = l_Lean_instToExprInt_mkNat(v___x_1526_);
v___x_1528_ = l_Lean_mkApp3(v___x_1522_, v___x_1523_, v___x_1524_, v___x_1527_);
v___y_1502_ = v_a_1518_;
v___y_1503_ = v___x_1528_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = l_Int_toNat(v_k_1519_);
v___x_1530_ = l_Lean_instToExprInt_mkNat(v___x_1529_);
v___y_1502_ = v_a_1518_;
v___y_1503_ = v___x_1530_;
goto v___jp_1501_;
}
}
else
{
lean_dec_ref(v_huv_1478_);
lean_dec_ref(v_v_1476_);
lean_dec_ref(v_u_1475_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(lean_object** _args){
lean_object* v_u_1537_ = _args[0];
lean_object* v_v_1538_ = _args[1];
lean_object* v_k_1539_ = _args[2];
lean_object* v_huv_1540_ = _args[3];
lean_object* v_k_x27_1541_ = _args[4];
lean_object* v_a_1542_ = _args[5];
lean_object* v_a_1543_ = _args[6];
lean_object* v_a_1544_ = _args[7];
lean_object* v_a_1545_ = _args[8];
lean_object* v_a_1546_ = _args[9];
lean_object* v_a_1547_ = _args[10];
lean_object* v_a_1548_ = _args[11];
lean_object* v_a_1549_ = _args[12];
lean_object* v_a_1550_ = _args[13];
lean_object* v_a_1551_ = _args[14];
lean_object* v_a_1552_ = _args[15];
lean_object* v_a_1553_ = _args[16];
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1537_, v_v_1538_, v_k_1539_, v_huv_1540_, v_k_x27_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_k_x27_1541_);
lean_dec_ref(v_k_1539_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object* v_u_1555_, lean_object* v_v_1556_, lean_object* v_k_1557_, lean_object* v_huv_1558_, lean_object* v_k_x27_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Meta_Grind_Order_isRing(v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; uint8_t v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1555_, v_v_1556_, v_k_1557_, v_huv_1558_, v_k_x27_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1555_, v_v_1556_, v_k_1557_, v_huv_1558_, v_k_x27_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1576_;
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_huv_1558_);
lean_dec_ref(v_v_1556_);
lean_dec_ref(v_u_1555_);
v_a_1577_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1572_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1572_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof___boxed(lean_object** _args){
lean_object* v_u_1585_ = _args[0];
lean_object* v_v_1586_ = _args[1];
lean_object* v_k_1587_ = _args[2];
lean_object* v_huv_1588_ = _args[3];
lean_object* v_k_x27_1589_ = _args[4];
lean_object* v_a_1590_ = _args[5];
lean_object* v_a_1591_ = _args[6];
lean_object* v_a_1592_ = _args[7];
lean_object* v_a_1593_ = _args[8];
lean_object* v_a_1594_ = _args[9];
lean_object* v_a_1595_ = _args[10];
lean_object* v_a_1596_ = _args[11];
lean_object* v_a_1597_ = _args[12];
lean_object* v_a_1598_ = _args[13];
lean_object* v_a_1599_ = _args[14];
lean_object* v_a_1600_ = _args[15];
lean_object* v_a_1601_ = _args[16];
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_u_1585_, v_v_1586_, v_k_1587_, v_huv_1588_, v_k_x27_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_k_x27_1589_);
lean_dec_ref(v_k_1587_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(lean_object* v_u_1615_, lean_object* v_k_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v_k_1635_; uint8_t v_strict_1636_; lean_object* v___y_1638_; 
v_k_1635_ = lean_ctor_get(v_k_1616_, 0);
v_strict_1636_ = lean_ctor_get_uint8(v_k_1616_, sizeof(void*)*1);
if (v_strict_1636_ == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1));
v___y_1638_ = v___x_1652_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3));
v___y_1638_ = v___x_1653_;
goto v___jp_1637_;
}
v___jp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = l_Lean_eagerReflBoolTrue;
v___x_1633_ = l_Lean_mkApp3(v___y_1630_, v_u_1615_, v___y_1631_, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
v___jp_1637_:
{
lean_object* v___x_1639_; 
lean_inc(v___y_1638_);
v___x_1639_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1638_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1642_ = lean_int_dec_le(v___x_1641_, v_k_1635_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1646_ = lean_int_neg(v_k_1635_);
v___x_1647_ = l_Int_toNat(v___x_1646_);
lean_dec(v___x_1646_);
v___x_1648_ = l_Lean_instToExprInt_mkNat(v___x_1647_);
v___x_1649_ = l_Lean_mkApp3(v___x_1643_, v___x_1644_, v___x_1645_, v___x_1648_);
v___y_1630_ = v_a_1640_;
v___y_1631_ = v___x_1649_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = l_Int_toNat(v_k_1635_);
v___x_1651_ = l_Lean_instToExprInt_mkNat(v___x_1650_);
v___y_1630_ = v_a_1640_;
v___y_1631_ = v___x_1651_;
goto v___jp_1629_;
}
}
else
{
lean_dec_ref(v_u_1615_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(lean_object* v_u_1654_, lean_object* v_k_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1654_, v_k_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_k_1655_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(lean_object* v_u_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1));
v___x_1689_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_1688_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = l_Lean_Expr_app___override(v_a_1690_, v_u_1675_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_dec_ref(v_u_1675_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___boxed(lean_object* v_u_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec(v_a_1700_);
return v_res_1712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1));
v___x_1716_ = lean_unsigned_to_nat(4u);
v___x_1717_ = lean_unsigned_to_nat(228u);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0));
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1720_ = l_mkPanicMessageWithDecl(v___x_1719_, v___x_1718_, v___x_1717_, v___x_1716_, v___x_1715_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object* v_u_1721_, lean_object* v_k_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Meta_Grind_Order_isRing(v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; uint8_t v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = lean_unbox(v_a_1736_);
lean_dec(v_a_1736_);
if (v___x_1737_ == 0)
{
uint8_t v_strict_1738_; 
v_strict_1738_ = lean_ctor_get_uint8(v_k_1722_, sizeof(void*)*1);
if (v_strict_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec_ref(v_u_1721_);
v___x_1739_ = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2);
v___x_1740_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1739_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1740_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1721_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1741_;
}
}
else
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1721_, v_k_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1742_;
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_u_1721_);
v_a_1743_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1735_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1735_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___boxed(lean_object* v_u_1751_, lean_object* v_k_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_u_1751_, v_k_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_k_1752_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(lean_object* v_u_1772_, lean_object* v_h_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
v___x_1787_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_1786_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1796_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = l_Lean_mkAppB(v_a_1788_, v_u_1772_, v_h_1773_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_dec_ref(v_h_1773_);
lean_dec_ref(v_u_1772_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___boxed(lean_object* v_u_1797_, lean_object* v_h_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_1797_, v_h_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec(v_a_1799_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(lean_object* v_u_1824_, lean_object* v_k_1825_, lean_object* v_h_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v_k_1845_; uint8_t v_strict_1846_; lean_object* v___y_1848_; 
v_k_1845_ = lean_ctor_get(v_k_1825_, 0);
v_strict_1846_ = lean_ctor_get_uint8(v_k_1825_, sizeof(void*)*1);
if (v_strict_1846_ == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
v___y_1848_ = v___x_1862_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
v___y_1848_ = v___x_1863_;
goto v___jp_1847_;
}
v___jp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_eagerReflBoolTrue;
v___x_1843_ = l_Lean_mkApp4(v___y_1840_, v_u_1824_, v___y_1841_, v___x_1842_, v_h_1826_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
v___jp_1847_:
{
lean_object* v___x_1849_; 
lean_inc(v___y_1848_);
v___x_1849_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1848_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1852_ = lean_int_dec_le(v___x_1851_, v_k_1845_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1856_ = lean_int_neg(v_k_1845_);
v___x_1857_ = l_Int_toNat(v___x_1856_);
lean_dec(v___x_1856_);
v___x_1858_ = l_Lean_instToExprInt_mkNat(v___x_1857_);
v___x_1859_ = l_Lean_mkApp3(v___x_1853_, v___x_1854_, v___x_1855_, v___x_1858_);
v___y_1840_ = v_a_1850_;
v___y_1841_ = v___x_1859_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = l_Int_toNat(v_k_1845_);
v___x_1861_ = l_Lean_instToExprInt_mkNat(v___x_1860_);
v___y_1840_ = v_a_1850_;
v___y_1841_ = v___x_1861_;
goto v___jp_1839_;
}
}
else
{
lean_dec_ref(v_h_1826_);
lean_dec_ref(v_u_1824_);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(lean_object* v_u_1864_, lean_object* v_k_1865_, lean_object* v_h_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_1864_, v_k_1865_, v_h_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_k_1865_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object* v_u_1880_, lean_object* v_k_1881_, lean_object* v_h_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_Grind_Order_isRing(v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_1880_, v_h_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_1880_, v_k_1881_, v_h_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
return v___x_1899_;
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v_h_1882_);
lean_dec_ref(v_u_1880_);
v_a_1900_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1895_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1895_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof___boxed(lean_object* v_u_1908_, lean_object* v_k_1909_, lean_object* v_h_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_u_1908_, v_k_1909_, v_h_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_k_1909_);
return v_res_1923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1));
v___x_1927_ = lean_unsigned_to_nat(2u);
v___x_1928_ = lean_unsigned_to_nat(255u);
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0));
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1931_ = l_mkPanicMessageWithDecl(v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(lean_object* v_u_1932_, lean_object* v_v_1933_, lean_object* v_k_u2081_1934_, lean_object* v_h_u2081_1935_, lean_object* v_k_u2082_1936_, lean_object* v_h_u2082_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
uint8_t v_strict_1950_; uint8_t v_strict_1951_; lean_object* v___x_1952_; 
v_strict_1950_ = lean_ctor_get_uint8(v_k_u2081_1934_, sizeof(void*)*1);
v_strict_1951_ = lean_ctor_get_uint8(v_k_u2082_1936_, sizeof(void*)*1);
lean_inc_ref_n(v_u_1932_, 2);
v___x_1952_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_1932_, v_v_1933_, v_u_1932_, v_strict_1950_, v_strict_1951_, v_h_u2081_1935_, v_h_u2082_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
if (v_strict_1950_ == 0)
{
if (v_strict_1951_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec(v_a_1953_);
lean_dec_ref(v_u_1932_);
v___x_1966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2);
v___x_1967_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1966_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1967_;
}
else
{
goto v___jp_1954_;
}
}
else
{
goto v___jp_1954_;
}
v___jp_1954_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
v___x_1956_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_1955_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = l_Lean_mkAppB(v_a_1957_, v_u_1932_, v_a_1953_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_dec(v_a_1953_);
lean_dec_ref(v_u_1932_);
return v___x_1956_;
}
}
}
else
{
lean_dec_ref(v_u_1932_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___boxed(lean_object** _args){
lean_object* v_u_1968_ = _args[0];
lean_object* v_v_1969_ = _args[1];
lean_object* v_k_u2081_1970_ = _args[2];
lean_object* v_h_u2081_1971_ = _args[3];
lean_object* v_k_u2082_1972_ = _args[4];
lean_object* v_h_u2082_1973_ = _args[5];
lean_object* v_a_1974_ = _args[6];
lean_object* v_a_1975_ = _args[7];
lean_object* v_a_1976_ = _args[8];
lean_object* v_a_1977_ = _args[9];
lean_object* v_a_1978_ = _args[10];
lean_object* v_a_1979_ = _args[11];
lean_object* v_a_1980_ = _args[12];
lean_object* v_a_1981_ = _args[13];
lean_object* v_a_1982_ = _args[14];
lean_object* v_a_1983_ = _args[15];
lean_object* v_a_1984_ = _args[16];
lean_object* v_a_1985_ = _args[17];
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_1968_, v_v_1969_, v_k_u2081_1970_, v_h_u2081_1971_, v_k_u2082_1972_, v_h_u2082_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_k_u2082_1972_);
lean_dec_ref(v_k_u2081_1970_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(lean_object* v_u_1987_, lean_object* v_v_1988_, lean_object* v_k_u2081_1989_, lean_object* v_h_u2081_1990_, lean_object* v_k_u2082_1991_, lean_object* v_h_u2082_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2005_; 
lean_inc_ref_n(v_u_1987_, 2);
v___x_2005_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_1987_, v_v_1988_, v_u_1987_, v_k_u2081_1989_, v_k_u2082_1991_, v_h_u2081_1990_, v_h_u2082_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2041_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2041_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2041_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v_k_2018_; uint8_t v_strict_2019_; lean_object* v___y_2021_; 
v_k_2018_ = lean_ctor_get(v_k_u2081_1989_, 0);
v_strict_2019_ = lean_ctor_get_uint8(v_k_u2081_1989_, sizeof(void*)*1);
if (v_strict_2019_ == 0)
{
uint8_t v_strict_2039_; 
v_strict_2039_ = lean_ctor_get_uint8(v_k_u2082_1991_, sizeof(void*)*1);
if (v_strict_2039_ == 0)
{
lean_object* v___x_2040_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
v___y_2021_ = v___x_2040_;
goto v___jp_2020_;
}
else
{
goto v___jp_2037_;
}
}
else
{
goto v___jp_2037_;
}
v___jp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2013_ = l_Lean_eagerReflBoolTrue;
v___x_2014_ = l_Lean_mkApp4(v___y_2011_, v_u_1987_, v___y_2012_, v___x_2013_, v_a_2006_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2014_);
v___x_2016_ = v___x_2008_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
v___jp_2020_:
{
lean_object* v___x_2022_; 
lean_inc(v___y_2021_);
v___x_2022_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_2021_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v_k_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2022_);
v_k_2024_ = lean_ctor_get(v_k_u2082_1991_, 0);
v___x_2025_ = lean_int_add(v_k_2018_, v_k_2024_);
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_2027_ = lean_int_dec_le(v___x_2026_, v___x_2025_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_2029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_2030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_2031_ = lean_int_neg(v___x_2025_);
lean_dec(v___x_2025_);
v___x_2032_ = l_Int_toNat(v___x_2031_);
lean_dec(v___x_2031_);
v___x_2033_ = l_Lean_instToExprInt_mkNat(v___x_2032_);
v___x_2034_ = l_Lean_mkApp3(v___x_2028_, v___x_2029_, v___x_2030_, v___x_2033_);
v___y_2011_ = v_a_2023_;
v___y_2012_ = v___x_2034_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = l_Int_toNat(v___x_2025_);
lean_dec(v___x_2025_);
v___x_2036_ = l_Lean_instToExprInt_mkNat(v___x_2035_);
v___y_2011_ = v_a_2023_;
v___y_2012_ = v___x_2036_;
goto v___jp_2010_;
}
}
else
{
lean_del_object(v___x_2008_);
lean_dec(v_a_2006_);
lean_dec_ref(v_u_1987_);
return v___x_2022_;
}
}
v___jp_2037_:
{
lean_object* v___x_2038_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
v___y_2021_ = v___x_2038_;
goto v___jp_2020_;
}
}
}
else
{
lean_dec_ref(v_u_1987_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset___boxed(lean_object** _args){
lean_object* v_u_2042_ = _args[0];
lean_object* v_v_2043_ = _args[1];
lean_object* v_k_u2081_2044_ = _args[2];
lean_object* v_h_u2081_2045_ = _args[3];
lean_object* v_k_u2082_2046_ = _args[4];
lean_object* v_h_u2082_2047_ = _args[5];
lean_object* v_a_2048_ = _args[6];
lean_object* v_a_2049_ = _args[7];
lean_object* v_a_2050_ = _args[8];
lean_object* v_a_2051_ = _args[9];
lean_object* v_a_2052_ = _args[10];
lean_object* v_a_2053_ = _args[11];
lean_object* v_a_2054_ = _args[12];
lean_object* v_a_2055_ = _args[13];
lean_object* v_a_2056_ = _args[14];
lean_object* v_a_2057_ = _args[15];
lean_object* v_a_2058_ = _args[16];
lean_object* v_a_2059_ = _args[17];
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2042_, v_v_2043_, v_k_u2081_2044_, v_h_u2081_2045_, v_k_u2082_2046_, v_h_u2082_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_k_u2082_2046_);
lean_dec_ref(v_k_u2081_2044_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object* v_u_2061_, lean_object* v_v_2062_, lean_object* v_k_u2081_2063_, lean_object* v_h_u2081_2064_, lean_object* v_k_u2082_2065_, lean_object* v_h_u2082_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Meta_Grind_Order_isRing(v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; uint8_t v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = lean_unbox(v_a_2080_);
lean_dec(v_a_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_2061_, v_v_2062_, v_k_u2081_2063_, v_h_u2081_2064_, v_k_u2082_2065_, v_h_u2082_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; 
v___x_2083_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2061_, v_v_2062_, v_k_u2081_2063_, v_h_u2081_2064_, v_k_u2082_2065_, v_h_u2082_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2083_;
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v_h_u2082_2066_);
lean_dec_ref(v_h_u2081_2064_);
lean_dec_ref(v_v_2062_);
lean_dec_ref(v_u_2061_);
v_a_2084_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2079_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2079_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof___boxed(lean_object** _args){
lean_object* v_u_2092_ = _args[0];
lean_object* v_v_2093_ = _args[1];
lean_object* v_k_u2081_2094_ = _args[2];
lean_object* v_h_u2081_2095_ = _args[3];
lean_object* v_k_u2082_2096_ = _args[4];
lean_object* v_h_u2082_2097_ = _args[5];
lean_object* v_a_2098_ = _args[6];
lean_object* v_a_2099_ = _args[7];
lean_object* v_a_2100_ = _args[8];
lean_object* v_a_2101_ = _args[9];
lean_object* v_a_2102_ = _args[10];
lean_object* v_a_2103_ = _args[11];
lean_object* v_a_2104_ = _args[12];
lean_object* v_a_2105_ = _args[13];
lean_object* v_a_2106_ = _args[14];
lean_object* v_a_2107_ = _args[15];
lean_object* v_a_2108_ = _args[16];
lean_object* v_a_2109_ = _args[17];
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_u_2092_, v_v_2093_, v_k_u2081_2094_, v_h_u2081_2095_, v_k_u2082_2096_, v_h_u2082_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_k_u2082_2096_);
lean_dec_ref(v_k_u2081_2094_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(lean_object* v_u_2117_, lean_object* v_v_2118_, lean_object* v_h_u2081_2119_, lean_object* v_h_u2082_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1));
v___x_2134_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_2133_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2143_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2143_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2143_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = l_Lean_mkApp4(v_a_2135_, v_u_2117_, v_v_2118_, v_h_u2081_2119_, v_h_u2082_2120_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
else
{
lean_dec_ref(v_h_u2082_2120_);
lean_dec_ref(v_h_u2081_2119_);
lean_dec_ref(v_v_2118_);
lean_dec_ref(v_u_2117_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___boxed(lean_object* v_u_2144_, lean_object* v_v_2145_, lean_object* v_h_u2081_2146_, lean_object* v_h_u2082_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2144_, v_v_2145_, v_h_u2081_2146_, v_h_u2082_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec(v_a_2148_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(lean_object* v_u_2167_, lean_object* v_v_2168_, lean_object* v_h_u2081_2169_, lean_object* v_h_u2082_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1));
v___x_2184_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_2183_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2184_);
v___x_2186_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2202_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2202_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2202_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___y_2192_; lean_object* v_ringInst_x3f_2198_; 
v_ringInst_x3f_2198_ = lean_ctor_get(v_a_2187_, 10);
lean_inc(v_ringInst_x3f_2198_);
lean_dec(v_a_2187_);
if (lean_obj_tag(v_ringInst_x3f_2198_) == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_2200_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2199_);
v___y_2192_ = v___x_2200_;
goto v___jp_2191_;
}
else
{
lean_object* v_val_2201_; 
v_val_2201_ = lean_ctor_get(v_ringInst_x3f_2198_, 0);
lean_inc(v_val_2201_);
lean_dec_ref(v_ringInst_x3f_2198_);
v___y_2192_ = v_val_2201_;
goto v___jp_2191_;
}
v___jp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = l_Lean_Expr_app___override(v_a_2185_, v___y_2192_);
v___x_2194_ = l_Lean_mkApp4(v___x_2193_, v_u_2167_, v_v_2168_, v_h_u2081_2169_, v_h_u2082_2170_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2194_);
v___x_2196_ = v___x_2189_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_a_2185_);
lean_dec_ref(v_h_u2082_2170_);
lean_dec_ref(v_h_u2081_2169_);
lean_dec_ref(v_v_2168_);
lean_dec_ref(v_u_2167_);
v_a_2203_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2186_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2186_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2082_2170_);
lean_dec_ref(v_h_u2081_2169_);
lean_dec_ref(v_v_2168_);
lean_dec_ref(v_u_2167_);
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___boxed(lean_object* v_u_2211_, lean_object* v_v_2212_, lean_object* v_h_u2081_2213_, lean_object* v_h_u2082_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2211_, v_v_2212_, v_h_u2081_2213_, v_h_u2082_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec(v_a_2215_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object* v_u_2228_, lean_object* v_v_2229_, lean_object* v_h_u2081_2230_, lean_object* v_h_u2082_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Meta_Grind_Order_isRing(v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; uint8_t v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2228_, v_v_2229_, v_h_u2081_2230_, v_h_u2082_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2228_, v_v_2229_, v_h_u2081_2230_, v_h_u2082_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2248_;
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_h_u2082_2231_);
lean_dec_ref(v_h_u2081_2230_);
lean_dec_ref(v_v_2229_);
lean_dec_ref(v_u_2228_);
v_a_2249_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2244_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2244_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe___boxed(lean_object* v_u_2257_, lean_object* v_v_2258_, lean_object* v_h_u2081_2259_, lean_object* v_h_u2082_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_u_2257_, v_v_2258_, v_h_u2081_2259_, v_h_u2082_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec(v_a_2261_);
return v_res_2273_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Order(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
