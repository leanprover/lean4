// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Proof
// Imports: public import Lean.Meta.Tactic.Grind.Order.OrderM public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Lean.OrderLevel import Init.Grind.Order
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
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_isPartialInst_x3f_86_, 1);
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
lean_dec_ref_known(v_ltInst_x3f_143_, 1);
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
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_144_, 1);
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
lean_dec_ref_known(v___x_199_, 1);
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
lean_dec_ref_known(v___x_247_, 1);
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
lean_dec_ref_known(v_isLinearPreInst_x3f_260_, 1);
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
lean_dec_ref_known(v_isLinearPreInst_x3f_308_, 1);
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
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = l_Lean_leCarrierIsSort(v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; uint8_t v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_unbox(v_a_360_);
lean_dec(v_a_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_384_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_384_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_384_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_384_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v_ringInst_x3f_374_; lean_object* v_orderedRingInst_x3f_375_; lean_object* v___y_377_; 
v_ringInst_x3f_374_ = lean_ctor_get(v_a_358_, 10);
lean_inc(v_ringInst_x3f_374_);
v_orderedRingInst_x3f_375_ = lean_ctor_get(v_a_358_, 11);
lean_inc(v_orderedRingInst_x3f_375_);
lean_dec(v_a_358_);
if (lean_obj_tag(v_ringInst_x3f_374_) == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_382_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_381_);
v___y_377_ = v___x_382_;
goto v___jp_376_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v_ringInst_x3f_374_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_ringInst_x3f_374_, 1);
v___y_377_ = v_val_383_;
goto v___jp_376_;
}
v___jp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = l_Lean_mkAppB(v_a_363_, v___y_368_, v___y_369_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_370_);
v___x_372_ = v___x_365_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
v___jp_376_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_375_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_379_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_378_);
v___y_368_ = v___y_377_;
v___y_369_ = v___x_379_;
goto v___jp_367_;
}
else
{
lean_object* v_val_380_; 
v_val_380_ = lean_ctor_get(v_orderedRingInst_x3f_375_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v_orderedRingInst_x3f_375_, 1);
v___y_368_ = v___y_377_;
v___y_369_ = v_val_380_;
goto v___jp_367_;
}
}
}
}
else
{
lean_dec(v_a_358_);
return v___x_362_;
}
}
else
{
lean_object* v_type_385_; lean_object* v_u_386_; lean_object* v_isPreorderInst_387_; lean_object* v_leInst_388_; lean_object* v_ltInst_x3f_389_; lean_object* v_lawfulOrderLTInst_x3f_390_; lean_object* v_ringInst_x3f_391_; lean_object* v_orderedRingInst_x3f_392_; lean_object* v___x_393_; 
v_type_385_ = lean_ctor_get(v_a_358_, 1);
lean_inc_ref(v_type_385_);
v_u_386_ = lean_ctor_get(v_a_358_, 2);
lean_inc(v_u_386_);
v_isPreorderInst_387_ = lean_ctor_get(v_a_358_, 3);
lean_inc_ref(v_isPreorderInst_387_);
v_leInst_388_ = lean_ctor_get(v_a_358_, 4);
lean_inc_ref(v_leInst_388_);
v_ltInst_x3f_389_ = lean_ctor_get(v_a_358_, 5);
lean_inc(v_ltInst_x3f_389_);
v_lawfulOrderLTInst_x3f_390_ = lean_ctor_get(v_a_358_, 8);
lean_inc(v_lawfulOrderLTInst_x3f_390_);
v_ringInst_x3f_391_ = lean_ctor_get(v_a_358_, 10);
lean_inc(v_ringInst_x3f_391_);
v_orderedRingInst_x3f_392_ = lean_ctor_get(v_a_358_, 11);
lean_inc(v_orderedRingInst_x3f_392_);
lean_dec(v_a_358_);
v___x_393_ = l_Lean_Meta_decLevel(v_u_386_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_431_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_431_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_431_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_431_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_424_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v_a_394_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = l_Lean_mkConst(v_declName_344_, v___x_399_);
if (lean_obj_tag(v_ltInst_x3f_389_) == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_429_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_428_);
v___y_424_ = v___x_429_;
goto v___jp_423_;
}
else
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v_ltInst_x3f_389_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_ltInst_x3f_389_, 1);
v___y_424_ = v_val_430_;
goto v___jp_423_;
}
v___jp_401_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = l_Lean_mkApp7(v___x_400_, v_type_385_, v_leInst_388_, v___y_403_, v___y_404_, v_isPreorderInst_387_, v___y_402_, v___y_405_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_406_);
v___x_408_ = v___x_396_;
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
v___jp_410_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_392_) == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_415_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_414_);
v___y_402_ = v___y_413_;
v___y_403_ = v___y_411_;
v___y_404_ = v___y_412_;
v___y_405_ = v___x_415_;
goto v___jp_401_;
}
else
{
lean_object* v_val_416_; 
v_val_416_ = lean_ctor_get(v_orderedRingInst_x3f_392_, 0);
lean_inc(v_val_416_);
lean_dec_ref_known(v_orderedRingInst_x3f_392_, 1);
v___y_402_ = v___y_413_;
v___y_403_ = v___y_411_;
v___y_404_ = v___y_412_;
v___y_405_ = v_val_416_;
goto v___jp_401_;
}
}
v___jp_417_:
{
if (lean_obj_tag(v_ringInst_x3f_391_) == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_421_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_420_);
v___y_411_ = v___y_418_;
v___y_412_ = v___y_419_;
v___y_413_ = v___x_421_;
goto v___jp_410_;
}
else
{
lean_object* v_val_422_; 
v_val_422_ = lean_ctor_get(v_ringInst_x3f_391_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_ringInst_x3f_391_, 1);
v___y_411_ = v___y_418_;
v___y_412_ = v___y_419_;
v___y_413_ = v_val_422_;
goto v___jp_410_;
}
}
v___jp_423_:
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_390_) == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_426_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_425_);
v___y_418_ = v___y_424_;
v___y_419_ = v___x_426_;
goto v___jp_417_;
}
else
{
lean_object* v_val_427_; 
v_val_427_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_390_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_390_, 1);
v___y_418_ = v___y_424_;
v___y_419_ = v_val_427_;
goto v___jp_417_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_orderedRingInst_x3f_392_);
lean_dec(v_ringInst_x3f_391_);
lean_dec(v_lawfulOrderLTInst_x3f_390_);
lean_dec(v_ltInst_x3f_389_);
lean_dec_ref(v_leInst_388_);
lean_dec_ref(v_isPreorderInst_387_);
lean_dec_ref(v_type_385_);
lean_dec(v_declName_344_);
v_a_432_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_393_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_393_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_a_358_);
lean_dec(v_declName_344_);
v_a_440_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_359_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_359_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_declName_344_);
v_a_448_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_357_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_357_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix___boxed(lean_object* v_declName_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v_declName_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec(v_a_458_);
lean_dec(v_a_457_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(lean_object* v_declName_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Grind_Order_getStruct(v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = l_Lean_leCarrierIsSort(v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; uint8_t v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = lean_unbox(v_a_486_);
lean_dec(v_a_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v_declName_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_510_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_510_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_510_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_510_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v_ringInst_x3f_500_; lean_object* v_orderedRingInst_x3f_501_; lean_object* v___y_503_; 
v_ringInst_x3f_500_ = lean_ctor_get(v_a_484_, 10);
lean_inc(v_ringInst_x3f_500_);
v_orderedRingInst_x3f_501_ = lean_ctor_get(v_a_484_, 11);
lean_inc(v_orderedRingInst_x3f_501_);
lean_dec(v_a_484_);
if (lean_obj_tag(v_ringInst_x3f_500_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_508_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_507_);
v___y_503_ = v___x_508_;
goto v___jp_502_;
}
else
{
lean_object* v_val_509_; 
v_val_509_ = lean_ctor_get(v_ringInst_x3f_500_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_ringInst_x3f_500_, 1);
v___y_503_ = v_val_509_;
goto v___jp_502_;
}
v___jp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_mkAppB(v_a_489_, v___y_494_, v___y_495_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_496_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
v___jp_502_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_501_) == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_505_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_504_);
v___y_494_ = v___y_503_;
v___y_495_ = v___x_505_;
goto v___jp_493_;
}
else
{
lean_object* v_val_506_; 
v_val_506_ = lean_ctor_get(v_orderedRingInst_x3f_501_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_orderedRingInst_x3f_501_, 1);
v___y_494_ = v___y_503_;
v___y_495_ = v_val_506_;
goto v___jp_493_;
}
}
}
}
else
{
lean_dec(v_a_484_);
return v___x_488_;
}
}
else
{
lean_object* v_type_511_; lean_object* v_u_512_; lean_object* v_leInst_513_; lean_object* v_ltInst_x3f_514_; lean_object* v_isLinearPreInst_x3f_515_; lean_object* v_lawfulOrderLTInst_x3f_516_; lean_object* v_ringInst_x3f_517_; lean_object* v_orderedRingInst_x3f_518_; lean_object* v___x_519_; 
v_type_511_ = lean_ctor_get(v_a_484_, 1);
lean_inc_ref(v_type_511_);
v_u_512_ = lean_ctor_get(v_a_484_, 2);
lean_inc(v_u_512_);
v_leInst_513_ = lean_ctor_get(v_a_484_, 4);
lean_inc_ref(v_leInst_513_);
v_ltInst_x3f_514_ = lean_ctor_get(v_a_484_, 5);
lean_inc(v_ltInst_x3f_514_);
v_isLinearPreInst_x3f_515_ = lean_ctor_get(v_a_484_, 7);
lean_inc(v_isLinearPreInst_x3f_515_);
v_lawfulOrderLTInst_x3f_516_ = lean_ctor_get(v_a_484_, 8);
lean_inc(v_lawfulOrderLTInst_x3f_516_);
v_ringInst_x3f_517_ = lean_ctor_get(v_a_484_, 10);
lean_inc(v_ringInst_x3f_517_);
v_orderedRingInst_x3f_518_ = lean_ctor_get(v_a_484_, 11);
lean_inc(v_orderedRingInst_x3f_518_);
lean_dec(v_a_484_);
v___x_519_ = l_Lean_Meta_decLevel(v_u_512_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_566_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_566_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_566_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_566_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_559_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v_a_520_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_mkConst(v_declName_470_, v___x_525_);
if (lean_obj_tag(v_ltInst_x3f_514_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_564_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_563_);
v___y_559_ = v___x_564_;
goto v___jp_558_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v_ltInst_x3f_514_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v_ltInst_x3f_514_, 1);
v___y_559_ = v_val_565_;
goto v___jp_558_;
}
v___jp_527_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = l_Lean_mkApp7(v___x_526_, v_type_511_, v_leInst_513_, v___y_529_, v___y_528_, v___y_530_, v___y_531_, v___y_532_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_533_);
v___x_535_ = v___x_522_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
v___jp_537_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_518_) == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_543_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_542_);
v___y_528_ = v___y_539_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
v___y_532_ = v___x_543_;
goto v___jp_527_;
}
else
{
lean_object* v_val_544_; 
v_val_544_ = lean_ctor_get(v_orderedRingInst_x3f_518_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v_orderedRingInst_x3f_518_, 1);
v___y_528_ = v___y_539_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
v___y_532_ = v_val_544_;
goto v___jp_527_;
}
}
v___jp_545_:
{
if (lean_obj_tag(v_ringInst_x3f_517_) == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_550_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_549_);
v___y_538_ = v___y_547_;
v___y_539_ = v___y_546_;
v___y_540_ = v___y_548_;
v___y_541_ = v___x_550_;
goto v___jp_537_;
}
else
{
lean_object* v_val_551_; 
v_val_551_ = lean_ctor_get(v_ringInst_x3f_517_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_ringInst_x3f_517_, 1);
v___y_538_ = v___y_547_;
v___y_539_ = v___y_546_;
v___y_540_ = v___y_548_;
v___y_541_ = v_val_551_;
goto v___jp_537_;
}
}
v___jp_552_:
{
if (lean_obj_tag(v_isLinearPreInst_x3f_515_) == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_556_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_555_);
v___y_546_ = v___y_554_;
v___y_547_ = v___y_553_;
v___y_548_ = v___x_556_;
goto v___jp_545_;
}
else
{
lean_object* v_val_557_; 
v_val_557_ = lean_ctor_get(v_isLinearPreInst_x3f_515_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v_isLinearPreInst_x3f_515_, 1);
v___y_546_ = v___y_554_;
v___y_547_ = v___y_553_;
v___y_548_ = v_val_557_;
goto v___jp_545_;
}
}
v___jp_558_:
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_516_) == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_561_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_560_);
v___y_553_ = v___y_559_;
v___y_554_ = v___x_561_;
goto v___jp_552_;
}
else
{
lean_object* v_val_562_; 
v_val_562_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_516_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_516_, 1);
v___y_553_ = v___y_559_;
v___y_554_ = v_val_562_;
goto v___jp_552_;
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_orderedRingInst_x3f_518_);
lean_dec(v_ringInst_x3f_517_);
lean_dec(v_lawfulOrderLTInst_x3f_516_);
lean_dec(v_isLinearPreInst_x3f_515_);
lean_dec(v_ltInst_x3f_514_);
lean_dec_ref(v_leInst_513_);
lean_dec_ref(v_type_511_);
lean_dec(v_declName_470_);
v_a_567_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_519_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_519_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_a_484_);
lean_dec(v_declName_470_);
v_a_575_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_485_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_485_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_declName_470_);
v_a_583_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_483_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_483_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix___boxed(lean_object* v_declName_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v_declName_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec(v_a_593_);
lean_dec(v_a_592_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(lean_object* v_u_632_, lean_object* v_v_633_, lean_object* v_w_634_, uint8_t v_strict_u2081_635_, uint8_t v_strict_u2082_636_, lean_object* v_h_u2081_637_, lean_object* v_h_u2082_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_h_652_; 
if (v_strict_u2081_635_ == 0)
{
if (v_strict_u2082_636_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4));
v___x_656_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_655_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v_h_652_ = v_a_657_;
goto v___jp_651_;
}
else
{
lean_dec_ref(v_h_u2082_638_);
lean_dec_ref(v_h_u2081_637_);
lean_dec_ref(v_w_634_);
lean_dec_ref(v_v_633_);
lean_dec_ref(v_u_632_);
return v___x_656_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6));
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_658_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v_h_652_ = v_a_660_;
goto v___jp_651_;
}
else
{
lean_dec_ref(v_h_u2082_638_);
lean_dec_ref(v_h_u2081_637_);
lean_dec_ref(v_w_634_);
lean_dec_ref(v_v_633_);
lean_dec_ref(v_u_632_);
return v___x_659_;
}
}
}
else
{
if (v_strict_u2082_636_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8));
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_661_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v_h_652_ = v_a_663_;
goto v___jp_651_;
}
else
{
lean_dec_ref(v_h_u2082_638_);
lean_dec_ref(v_h_u2081_637_);
lean_dec_ref(v_w_634_);
lean_dec_ref(v_v_633_);
lean_dec_ref(v_u_632_);
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10));
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_664_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_h_652_ = v_a_666_;
goto v___jp_651_;
}
else
{
lean_dec_ref(v_h_u2082_638_);
lean_dec_ref(v_h_u2081_637_);
lean_dec_ref(v_w_634_);
lean_dec_ref(v_v_633_);
lean_dec_ref(v_u_632_);
return v___x_665_;
}
}
}
v___jp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = l_Lean_mkApp5(v_h_652_, v_u_632_, v_v_633_, v_w_634_, v_h_u2081_637_, v_h_u2082_638_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(lean_object** _args){
lean_object* v_u_667_ = _args[0];
lean_object* v_v_668_ = _args[1];
lean_object* v_w_669_ = _args[2];
lean_object* v_strict_u2081_670_ = _args[3];
lean_object* v_strict_u2082_671_ = _args[4];
lean_object* v_h_u2081_672_ = _args[5];
lean_object* v_h_u2082_673_ = _args[6];
lean_object* v_a_674_ = _args[7];
lean_object* v_a_675_ = _args[8];
lean_object* v_a_676_ = _args[9];
lean_object* v_a_677_ = _args[10];
lean_object* v_a_678_ = _args[11];
lean_object* v_a_679_ = _args[12];
lean_object* v_a_680_ = _args[13];
lean_object* v_a_681_ = _args[14];
lean_object* v_a_682_ = _args[15];
lean_object* v_a_683_ = _args[16];
lean_object* v_a_684_ = _args[17];
lean_object* v_a_685_ = _args[18];
_start:
{
uint8_t v_strict_u2081_boxed_686_; uint8_t v_strict_u2082_boxed_687_; lean_object* v_res_688_; 
v_strict_u2081_boxed_686_ = lean_unbox(v_strict_u2081_670_);
v_strict_u2082_boxed_687_ = lean_unbox(v_strict_u2082_671_);
v_res_688_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_667_, v_v_668_, v_w_669_, v_strict_u2081_boxed_686_, v_strict_u2082_boxed_687_, v_h_u2081_672_, v_h_u2082_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
return v_res_688_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(lean_object* v_xs_689_, lean_object* v_i_690_){
_start:
{
lean_object* v_size_691_; uint8_t v___x_692_; 
v_size_691_ = lean_ctor_get(v_xs_689_, 2);
v___x_692_ = lean_nat_dec_lt(v_i_690_, v_size_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(lean_object* v_xs_693_, lean_object* v_i_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_xs_693_, v_i_694_);
lean_dec(v_i_694_);
lean_dec_ref(v_xs_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_nat_to_int(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(lean_object* v_p_u2081_699_, lean_object* v_p_u2082_700_, lean_object* v_v_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_w_714_; lean_object* v_k_715_; lean_object* v_proof_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_775_; 
v_w_714_ = lean_ctor_get(v_p_u2081_699_, 0);
v_k_715_ = lean_ctor_get(v_p_u2081_699_, 1);
v_proof_716_ = lean_ctor_get(v_p_u2081_699_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_p_u2081_699_);
if (v_isSharedCheck_775_ == 0)
{
v___x_718_ = v_p_u2081_699_;
v_isShared_719_ = v_isSharedCheck_775_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_proof_716_);
lean_inc(v_k_715_);
lean_inc(v_w_714_);
lean_dec(v_p_u2081_699_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_775_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; lean_object* v_k_729_; uint8_t v_strict_730_; lean_object* v_w_731_; lean_object* v_proof_732_; uint8_t v_strict_733_; lean_object* v___x_734_; 
v_k_729_ = lean_ctor_get(v_p_u2082_700_, 1);
lean_inc_ref(v_k_729_);
v_strict_730_ = lean_ctor_get_uint8(v_k_715_, sizeof(void*)*1);
lean_dec_ref(v_k_715_);
v_w_731_ = lean_ctor_get(v_p_u2082_700_, 0);
lean_inc(v_w_731_);
v_proof_732_ = lean_ctor_get(v_p_u2082_700_, 2);
lean_inc_ref(v_proof_732_);
lean_dec_ref(v_p_u2082_700_);
v_strict_733_ = lean_ctor_get_uint8(v_k_729_, sizeof(void*)*1);
lean_dec_ref(v_k_729_);
v___x_734_ = l_Lean_Meta_Grind_Order_getStruct(v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v_nodes_751_; lean_object* v___x_752_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_760_; uint8_t v___x_764_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v_nodes_751_ = lean_ctor_get(v_a_735_, 14);
lean_inc_ref(v_nodes_751_);
lean_dec(v_a_735_);
v___x_752_ = l_Lean_instInhabitedExpr;
v___x_764_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_751_, v_w_714_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = l_outOfBounds___redArg(v___x_752_);
v___y_760_ = v___x_765_;
goto v___jp_759_;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentArray_get_x21___redArg(v___x_752_, v_nodes_751_, v_w_714_);
v___y_760_ = v___x_766_;
goto v___jp_759_;
}
v___jp_736_:
{
lean_object* v___x_740_; 
v___x_740_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v___y_737_, v___y_738_, v___y_739_, v_strict_730_, v_strict_733_, v_proof_716_, v_proof_732_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
if (v_strict_730_ == 0)
{
v___y_721_ = v_a_741_;
v___y_722_ = v___x_742_;
v___y_723_ = v_strict_733_;
goto v___jp_720_;
}
else
{
v___y_721_ = v_a_741_;
v___y_722_ = v___x_742_;
v___y_723_ = v_strict_730_;
goto v___jp_720_;
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_del_object(v___x_718_);
lean_dec(v_w_714_);
v_a_743_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_740_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_740_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_753_:
{
uint8_t v___x_756_; 
v___x_756_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_751_, v_v_701_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v_nodes_751_);
v___x_757_ = l_outOfBounds___redArg(v___x_752_);
v___y_737_ = v___y_754_;
v___y_738_ = v___y_755_;
v___y_739_ = v___x_757_;
goto v___jp_736_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentArray_get_x21___redArg(v___x_752_, v_nodes_751_, v_v_701_);
lean_dec_ref(v_nodes_751_);
v___y_737_ = v___y_754_;
v___y_738_ = v___y_755_;
v___y_739_ = v___x_758_;
goto v___jp_736_;
}
}
v___jp_759_:
{
uint8_t v___x_761_; 
v___x_761_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_751_, v_w_731_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_w_731_);
v___x_762_ = l_outOfBounds___redArg(v___x_752_);
v___y_754_ = v___y_760_;
v___y_755_ = v___x_762_;
goto v___jp_753_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PersistentArray_get_x21___redArg(v___x_752_, v_nodes_751_, v_w_731_);
lean_dec(v_w_731_);
v___y_754_ = v___y_760_;
v___y_755_ = v___x_763_;
goto v___jp_753_;
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_proof_732_);
lean_dec(v_w_731_);
lean_del_object(v___x_718_);
lean_dec_ref(v_proof_716_);
lean_dec(v_w_714_);
v_a_767_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_734_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_734_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
v___jp_720_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
lean_inc(v___y_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_724_, 0, v___y_722_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*1, v___y_723_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v___y_721_);
lean_ctor_set(v___x_718_, 1, v___x_724_);
v___x_726_ = v___x_718_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_w_714_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___y_721_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(lean_object* v_p_u2081_776_, lean_object* v_p_u2082_777_, lean_object* v_v_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_776_, v_p_u2082_777_, v_v_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec(v_a_780_);
lean_dec(v_a_779_);
lean_dec(v_v_778_);
return v_res_791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Lean_Level_ofNat(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_box(0);
v___x_800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4);
v___x_803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2));
v___x_804_ = l_Lean_Expr_const___override(v___x_803_, v___x_802_);
return v___x_804_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_box(0);
v___x_809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7));
v___x_810_ = l_Lean_Expr_const___override(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_box(0);
v___x_816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10));
v___x_817_ = l_Lean_Expr_const___override(v___x_816_, v___x_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(lean_object* v_u_842_, lean_object* v_v_843_, lean_object* v_w_844_, lean_object* v_k_u2081_845_, lean_object* v_k_u2082_846_, lean_object* v_h_u2081_847_, lean_object* v_h_u2082_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v_k_902_; uint8_t v_strict_903_; lean_object* v_h_905_; 
v_k_902_ = lean_ctor_get(v_k_u2081_845_, 0);
v_strict_903_ = lean_ctor_get_uint8(v_k_u2081_845_, sizeof(void*)*1);
if (v_strict_903_ == 0)
{
uint8_t v_strict_919_; 
v_strict_919_ = lean_ctor_get_uint8(v_k_u2082_846_, sizeof(void*)*1);
if (v_strict_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13));
v___x_921_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_920_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v_h_905_ = v_a_922_;
goto v___jp_904_;
}
else
{
lean_dec_ref(v_h_u2082_848_);
lean_dec_ref(v_h_u2081_847_);
lean_dec_ref(v_w_844_);
lean_dec_ref(v_v_843_);
lean_dec_ref(v_u_842_);
return v___x_921_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15));
v___x_924_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_923_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_h_905_ = v_a_925_;
goto v___jp_904_;
}
else
{
lean_dec_ref(v_h_u2082_848_);
lean_dec_ref(v_h_u2081_847_);
lean_dec_ref(v_w_844_);
lean_dec_ref(v_v_843_);
lean_dec_ref(v_u_842_);
return v___x_924_;
}
}
}
else
{
uint8_t v_strict_926_; 
v_strict_926_ = lean_ctor_get_uint8(v_k_u2082_846_, sizeof(void*)*1);
if (v_strict_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17));
v___x_928_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_927_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v_h_905_ = v_a_929_;
goto v___jp_904_;
}
else
{
lean_dec_ref(v_h_u2082_848_);
lean_dec_ref(v_h_u2081_847_);
lean_dec_ref(v_w_844_);
lean_dec_ref(v_v_843_);
lean_dec_ref(v_u_842_);
return v___x_928_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19));
v___x_931_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_930_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v_h_905_ = v_a_932_;
goto v___jp_904_;
}
else
{
lean_dec_ref(v_h_u2082_848_);
lean_dec_ref(v_h_u2081_847_);
lean_dec_ref(v_w_844_);
lean_dec_ref(v_v_843_);
lean_dec_ref(v_u_842_);
return v___x_931_;
}
}
}
v___jp_861_:
{
lean_object* v_h_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_h_866_ = l_Lean_mkApp6(v___y_862_, v_u_842_, v_v_843_, v_w_844_, v___y_864_, v___y_863_, v___y_865_);
v___x_867_ = l_Lean_eagerReflBoolTrue;
v___x_868_ = l_Lean_mkApp3(v_h_866_, v_h_u2081_847_, v_h_u2082_848_, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
v___jp_870_:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_876_ = lean_int_dec_le(v___x_875_, v___y_872_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_880_ = lean_int_neg(v___y_872_);
lean_dec(v___y_872_);
v___x_881_ = l_Int_toNat(v___x_880_);
lean_dec(v___x_880_);
v___x_882_ = l_Lean_instToExprInt_mkNat(v___x_881_);
v___x_883_ = l_Lean_mkApp3(v___x_877_, v___x_878_, v___x_879_, v___x_882_);
v___y_862_ = v___y_871_;
v___y_863_ = v___y_874_;
v___y_864_ = v___y_873_;
v___y_865_ = v___x_883_;
goto v___jp_861_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = l_Int_toNat(v___y_872_);
lean_dec(v___y_872_);
v___x_885_ = l_Lean_instToExprInt_mkNat(v___x_884_);
v___y_862_ = v___y_871_;
v___y_863_ = v___y_874_;
v___y_864_ = v___y_873_;
v___y_865_ = v___x_885_;
goto v___jp_861_;
}
}
v___jp_886_:
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_892_ = lean_int_dec_le(v___x_891_, v___y_888_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_895_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_896_ = lean_int_neg(v___y_888_);
v___x_897_ = l_Int_toNat(v___x_896_);
lean_dec(v___x_896_);
v___x_898_ = l_Lean_instToExprInt_mkNat(v___x_897_);
v___x_899_ = l_Lean_mkApp3(v___x_893_, v___x_894_, v___x_895_, v___x_898_);
v___y_871_ = v___y_887_;
v___y_872_ = v___y_889_;
v___y_873_ = v___y_890_;
v___y_874_ = v___x_899_;
goto v___jp_870_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = l_Int_toNat(v___y_888_);
v___x_901_ = l_Lean_instToExprInt_mkNat(v___x_900_);
v___y_871_ = v___y_887_;
v___y_872_ = v___y_889_;
v___y_873_ = v___y_890_;
v___y_874_ = v___x_901_;
goto v___jp_870_;
}
}
v___jp_904_:
{
lean_object* v_k_906_; lean_object* v_k_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_k_906_ = lean_ctor_get(v_k_u2082_846_, 0);
v_k_907_ = lean_int_add(v_k_902_, v_k_906_);
v___x_908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_909_ = lean_int_dec_le(v___x_908_, v_k_902_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_913_ = lean_int_neg(v_k_902_);
v___x_914_ = l_Int_toNat(v___x_913_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_instToExprInt_mkNat(v___x_914_);
v___x_916_ = l_Lean_mkApp3(v___x_910_, v___x_911_, v___x_912_, v___x_915_);
v___y_887_ = v_h_905_;
v___y_888_ = v_k_906_;
v___y_889_ = v_k_907_;
v___y_890_ = v___x_916_;
goto v___jp_886_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = l_Int_toNat(v_k_902_);
v___x_918_ = l_Lean_instToExprInt_mkNat(v___x_917_);
v___y_887_ = v_h_905_;
v___y_888_ = v_k_906_;
v___y_889_ = v_k_907_;
v___y_890_ = v___x_918_;
goto v___jp_886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(lean_object** _args){
lean_object* v_u_933_ = _args[0];
lean_object* v_v_934_ = _args[1];
lean_object* v_w_935_ = _args[2];
lean_object* v_k_u2081_936_ = _args[3];
lean_object* v_k_u2082_937_ = _args[4];
lean_object* v_h_u2081_938_ = _args[5];
lean_object* v_h_u2082_939_ = _args[6];
lean_object* v_a_940_ = _args[7];
lean_object* v_a_941_ = _args[8];
lean_object* v_a_942_ = _args[9];
lean_object* v_a_943_ = _args[10];
lean_object* v_a_944_ = _args[11];
lean_object* v_a_945_ = _args[12];
lean_object* v_a_946_ = _args[13];
lean_object* v_a_947_ = _args[14];
lean_object* v_a_948_ = _args[15];
lean_object* v_a_949_ = _args[16];
lean_object* v_a_950_ = _args[17];
lean_object* v_a_951_ = _args[18];
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_933_, v_v_934_, v_w_935_, v_k_u2081_936_, v_k_u2082_937_, v_h_u2081_938_, v_h_u2082_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_k_u2082_937_);
lean_dec_ref(v_k_u2081_936_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(lean_object* v_p_u2081_953_, lean_object* v_p_u2082_954_, lean_object* v_v_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_w_968_; lean_object* v_k_969_; lean_object* v_proof_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1031_; 
v_w_968_ = lean_ctor_get(v_p_u2081_953_, 0);
v_k_969_ = lean_ctor_get(v_p_u2081_953_, 1);
v_proof_970_ = lean_ctor_get(v_p_u2081_953_, 2);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_p_u2081_953_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_972_ = v_p_u2081_953_;
v_isShared_973_ = v_isSharedCheck_1031_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_proof_970_);
lean_inc(v_k_969_);
lean_inc(v_w_968_);
lean_dec(v_p_u2081_953_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1031_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___y_975_; lean_object* v___y_976_; uint8_t v___y_977_; lean_object* v_w_983_; lean_object* v_k_984_; lean_object* v_proof_985_; lean_object* v___x_986_; 
v_w_983_ = lean_ctor_get(v_p_u2082_954_, 0);
lean_inc(v_w_983_);
v_k_984_ = lean_ctor_get(v_p_u2082_954_, 1);
lean_inc_ref(v_k_984_);
v_proof_985_ = lean_ctor_get(v_p_u2082_954_, 2);
lean_inc_ref(v_proof_985_);
lean_dec_ref(v_p_u2082_954_);
v___x_986_ = l_Lean_Meta_Grind_Order_getStruct(v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v_nodes_1007_; lean_object* v___x_1008_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1016_; uint8_t v___x_1020_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v_nodes_1007_ = lean_ctor_get(v_a_987_, 14);
lean_inc_ref(v_nodes_1007_);
lean_dec(v_a_987_);
v___x_1008_ = l_Lean_instInhabitedExpr;
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_1007_, v_w_968_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = l_outOfBounds___redArg(v___x_1008_);
v___y_1016_ = v___x_1021_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1008_, v_nodes_1007_, v_w_968_);
v___y_1016_ = v___x_1022_;
goto v___jp_1015_;
}
v___jp_988_:
{
lean_object* v___x_992_; 
v___x_992_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v___y_990_, v___y_989_, v___y_991_, v_k_969_, v_k_984_, v_proof_970_, v_proof_985_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_k_994_; uint8_t v_strict_995_; lean_object* v_k_996_; uint8_t v_strict_997_; lean_object* v___x_998_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v_k_994_ = lean_ctor_get(v_k_969_, 0);
lean_inc(v_k_994_);
v_strict_995_ = lean_ctor_get_uint8(v_k_969_, sizeof(void*)*1);
lean_dec_ref(v_k_969_);
v_k_996_ = lean_ctor_get(v_k_984_, 0);
lean_inc(v_k_996_);
v_strict_997_ = lean_ctor_get_uint8(v_k_984_, sizeof(void*)*1);
lean_dec_ref(v_k_984_);
v___x_998_ = lean_int_add(v_k_994_, v_k_996_);
lean_dec(v_k_996_);
lean_dec(v_k_994_);
if (v_strict_995_ == 0)
{
v___y_975_ = v___x_998_;
v___y_976_ = v_a_993_;
v___y_977_ = v_strict_997_;
goto v___jp_974_;
}
else
{
v___y_975_ = v___x_998_;
v___y_976_ = v_a_993_;
v___y_977_ = v_strict_995_;
goto v___jp_974_;
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_k_984_);
lean_del_object(v___x_972_);
lean_dec_ref(v_k_969_);
lean_dec(v_w_968_);
v_a_999_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_992_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_992_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
v___jp_1009_:
{
uint8_t v___x_1012_; 
v___x_1012_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_1007_, v_v_955_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref(v_nodes_1007_);
v___x_1013_ = l_outOfBounds___redArg(v___x_1008_);
v___y_989_ = v___y_1011_;
v___y_990_ = v___y_1010_;
v___y_991_ = v___x_1013_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1008_, v_nodes_1007_, v_v_955_);
lean_dec_ref(v_nodes_1007_);
v___y_989_ = v___y_1011_;
v___y_990_ = v___y_1010_;
v___y_991_ = v___x_1014_;
goto v___jp_988_;
}
}
v___jp_1015_:
{
uint8_t v___x_1017_; 
v___x_1017_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_1007_, v_w_983_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_w_983_);
v___x_1018_ = l_outOfBounds___redArg(v___x_1008_);
v___y_1010_ = v___y_1016_;
v___y_1011_ = v___x_1018_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1008_, v_nodes_1007_, v_w_983_);
lean_dec(v_w_983_);
v___y_1010_ = v___y_1016_;
v___y_1011_ = v___x_1019_;
goto v___jp_1009_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_proof_985_);
lean_dec_ref(v_k_984_);
lean_dec(v_w_983_);
lean_del_object(v___x_972_);
lean_dec_ref(v_proof_970_);
lean_dec_ref(v_k_969_);
lean_dec(v_w_968_);
v_a_1023_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_986_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_986_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
v___jp_974_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_978_, 0, v___y_975_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*1, v___y_977_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 2, v___y_976_);
lean_ctor_set(v___x_972_, 1, v___x_978_);
v___x_980_ = v___x_972_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_w_968_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v___y_976_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(lean_object* v_p_u2081_1032_, lean_object* v_p_u2082_1033_, lean_object* v_v_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_1032_, v_p_u2082_1033_, v_v_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec(v_v_1034_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object* v_p_u2081_1048_, lean_object* v_p_u2082_1049_, lean_object* v_v_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Grind_Order_isRing(v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; uint8_t v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = lean_unbox(v_a_1064_);
lean_dec(v_a_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_1048_, v_p_u2082_1049_, v_v_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_1048_, v_p_u2082_1049_, v_v_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1067_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_p_u2082_1049_);
lean_dec_ref(v_p_u2081_1048_);
v_a_1068_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1063_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1063_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkTrans___boxed(lean_object* v_p_u2081_1076_, lean_object* v_p_u2082_1077_, lean_object* v_v_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Meta_Grind_Order_mkTrans(v_p_u2081_1076_, v_p_u2082_1077_, v_v_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec(v_v_1078_);
return v_res_1091_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1910__overap_1108_; lean_object* v___x_1109_; 
v___x_1106_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0);
v___f_1107_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1107_, 0, v___x_1106_);
v___x_1910__overap_1108_ = lean_panic_fn_borrowed(v___f_1107_, v_msg_1093_);
lean_dec_ref(v___f_1107_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1099_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
lean_inc(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc(v___y_1094_);
v___x_1109_ = lean_apply_12(v___x_1910__overap_1108_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, lean_box(0));
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(lean_object* v_msg_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v_msg_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec(v___y_1111_);
return v_res_1123_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2));
v___x_1128_ = lean_unsigned_to_nat(4u);
v___x_1129_ = lean_unsigned_to_nat(146u);
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1));
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1132_ = l_mkPanicMessageWithDecl(v___x_1131_, v___x_1130_, v___x_1129_, v___x_1128_, v___x_1127_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(lean_object* v_u_1139_, lean_object* v_v_1140_, lean_object* v_k_1141_, lean_object* v_huv_1142_, lean_object* v_k_x27_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v_strict_1159_; uint8_t v_strict_1160_; 
v_strict_1159_ = lean_ctor_get_uint8(v_k_1141_, sizeof(void*)*1);
v_strict_1160_ = lean_ctor_get_uint8(v_k_x27_1143_, sizeof(void*)*1);
if (v_strict_1159_ == 0)
{
if (v_strict_1160_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v_v_1140_);
lean_dec_ref(v_u_1139_);
v___x_1173_ = l_Lean_Meta_mkEqTrue(v_huv_1142_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1173_;
}
else
{
goto v___jp_1161_;
}
}
else
{
if (v_strict_1160_ == 0)
{
goto v___jp_1161_;
}
else
{
lean_object* v___x_1174_; 
lean_dec_ref(v_v_1140_);
lean_dec_ref(v_u_1139_);
v___x_1174_ = l_Lean_Meta_mkEqTrue(v_huv_1142_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1174_;
}
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3);
v___x_1158_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1157_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1158_;
}
v___jp_1161_:
{
if (v_strict_1159_ == 0)
{
lean_dec_ref(v_huv_1142_);
lean_dec_ref(v_v_1140_);
lean_dec_ref(v_u_1139_);
goto v___jp_1156_;
}
else
{
if (v_strict_1160_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5));
v___x_1163_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_1162_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = l_Lean_mkApp3(v_a_1164_, v_u_1139_, v_v_1140_, v_huv_1142_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_dec_ref(v_huv_1142_);
lean_dec_ref(v_v_1140_);
lean_dec_ref(v_u_1139_);
return v___x_1163_;
}
}
else
{
lean_dec_ref(v_huv_1142_);
lean_dec_ref(v_v_1140_);
lean_dec_ref(v_u_1139_);
goto v___jp_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___boxed(lean_object** _args){
lean_object* v_u_1175_ = _args[0];
lean_object* v_v_1176_ = _args[1];
lean_object* v_k_1177_ = _args[2];
lean_object* v_huv_1178_ = _args[3];
lean_object* v_k_x27_1179_ = _args[4];
lean_object* v_a_1180_ = _args[5];
lean_object* v_a_1181_ = _args[6];
lean_object* v_a_1182_ = _args[7];
lean_object* v_a_1183_ = _args[8];
lean_object* v_a_1184_ = _args[9];
lean_object* v_a_1185_ = _args[10];
lean_object* v_a_1186_ = _args[11];
lean_object* v_a_1187_ = _args[12];
lean_object* v_a_1188_ = _args[13];
lean_object* v_a_1189_ = _args[14];
lean_object* v_a_1190_ = _args[15];
lean_object* v_a_1191_ = _args[16];
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1175_, v_v_1176_, v_k_1177_, v_huv_1178_, v_k_x27_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_k_x27_1179_);
lean_dec_ref(v_k_1177_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(lean_object* v_u_1217_, lean_object* v_v_1218_, lean_object* v_k_1219_, lean_object* v_huv_1220_, lean_object* v_k_x27_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v_k_1241_; uint8_t v_strict_1242_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1258_; 
v_k_1241_ = lean_ctor_get(v_k_x27_1221_, 0);
v_strict_1242_ = lean_ctor_get_uint8(v_k_x27_1221_, sizeof(void*)*1);
if (v_strict_1242_ == 0)
{
uint8_t v_strict_1273_; 
v_strict_1273_ = lean_ctor_get_uint8(v_k_1219_, sizeof(void*)*1);
if (v_strict_1273_ == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1));
v___y_1258_ = v___x_1274_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1275_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3));
v___y_1258_ = v___x_1275_;
goto v___jp_1257_;
}
}
else
{
uint8_t v_strict_1276_; 
v_strict_1276_ = lean_ctor_get_uint8(v_k_1219_, sizeof(void*)*1);
if (v_strict_1276_ == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5));
v___y_1258_ = v___x_1277_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7));
v___y_1258_ = v___x_1278_;
goto v___jp_1257_;
}
}
v___jp_1234_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_eagerReflBoolTrue;
v___x_1239_ = l_Lean_mkApp6(v___y_1235_, v_u_1217_, v_v_1218_, v___y_1236_, v___y_1237_, v___x_1238_, v_huv_1220_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
v___jp_1243_:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1247_ = lean_int_dec_le(v___x_1246_, v_k_1241_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1250_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1251_ = lean_int_neg(v_k_1241_);
v___x_1252_ = l_Int_toNat(v___x_1251_);
lean_dec(v___x_1251_);
v___x_1253_ = l_Lean_instToExprInt_mkNat(v___x_1252_);
v___x_1254_ = l_Lean_mkApp3(v___x_1248_, v___x_1249_, v___x_1250_, v___x_1253_);
v___y_1235_ = v___y_1244_;
v___y_1236_ = v___y_1245_;
v___y_1237_ = v___x_1254_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = l_Int_toNat(v_k_1241_);
v___x_1256_ = l_Lean_instToExprInt_mkNat(v___x_1255_);
v___y_1235_ = v___y_1244_;
v___y_1236_ = v___y_1245_;
v___y_1237_ = v___x_1256_;
goto v___jp_1234_;
}
}
v___jp_1257_:
{
lean_object* v___x_1259_; 
lean_inc(v___y_1258_);
v___x_1259_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1258_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_k_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v_k_1261_ = lean_ctor_get(v_k_1219_, 0);
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1263_ = lean_int_dec_le(v___x_1262_, v_k_1261_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1267_ = lean_int_neg(v_k_1261_);
v___x_1268_ = l_Int_toNat(v___x_1267_);
lean_dec(v___x_1267_);
v___x_1269_ = l_Lean_instToExprInt_mkNat(v___x_1268_);
v___x_1270_ = l_Lean_mkApp3(v___x_1264_, v___x_1265_, v___x_1266_, v___x_1269_);
v___y_1244_ = v_a_1260_;
v___y_1245_ = v___x_1270_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Int_toNat(v_k_1261_);
v___x_1272_ = l_Lean_instToExprInt_mkNat(v___x_1271_);
v___y_1244_ = v_a_1260_;
v___y_1245_ = v___x_1272_;
goto v___jp_1243_;
}
}
else
{
lean_dec_ref(v_huv_1220_);
lean_dec_ref(v_v_1218_);
lean_dec_ref(v_u_1217_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(lean_object** _args){
lean_object* v_u_1279_ = _args[0];
lean_object* v_v_1280_ = _args[1];
lean_object* v_k_1281_ = _args[2];
lean_object* v_huv_1282_ = _args[3];
lean_object* v_k_x27_1283_ = _args[4];
lean_object* v_a_1284_ = _args[5];
lean_object* v_a_1285_ = _args[6];
lean_object* v_a_1286_ = _args[7];
lean_object* v_a_1287_ = _args[8];
lean_object* v_a_1288_ = _args[9];
lean_object* v_a_1289_ = _args[10];
lean_object* v_a_1290_ = _args[11];
lean_object* v_a_1291_ = _args[12];
lean_object* v_a_1292_ = _args[13];
lean_object* v_a_1293_ = _args[14];
lean_object* v_a_1294_ = _args[15];
lean_object* v_a_1295_ = _args[16];
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1279_, v_v_1280_, v_k_1281_, v_huv_1282_, v_k_x27_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_k_x27_1283_);
lean_dec_ref(v_k_1281_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object* v_u_1297_, lean_object* v_v_1298_, lean_object* v_k_1299_, lean_object* v_huv_1300_, lean_object* v_k_x27_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_Grind_Order_isRing(v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_1297_, v_v_1298_, v_k_1299_, v_huv_1300_, v_k_x27_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_1297_, v_v_1298_, v_k_1299_, v_huv_1300_, v_k_x27_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1318_;
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_huv_1300_);
lean_dec_ref(v_v_1298_);
lean_dec_ref(v_u_1297_);
v_a_1319_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1314_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1314_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof___boxed(lean_object** _args){
lean_object* v_u_1327_ = _args[0];
lean_object* v_v_1328_ = _args[1];
lean_object* v_k_1329_ = _args[2];
lean_object* v_huv_1330_ = _args[3];
lean_object* v_k_x27_1331_ = _args[4];
lean_object* v_a_1332_ = _args[5];
lean_object* v_a_1333_ = _args[6];
lean_object* v_a_1334_ = _args[7];
lean_object* v_a_1335_ = _args[8];
lean_object* v_a_1336_ = _args[9];
lean_object* v_a_1337_ = _args[10];
lean_object* v_a_1338_ = _args[11];
lean_object* v_a_1339_ = _args[12];
lean_object* v_a_1340_ = _args[13];
lean_object* v_a_1341_ = _args[14];
lean_object* v_a_1342_ = _args[15];
lean_object* v_a_1343_ = _args[16];
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_u_1327_, v_v_1328_, v_k_1329_, v_huv_1330_, v_k_x27_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_k_x27_1331_);
lean_dec_ref(v_k_1329_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(lean_object* v_u_1357_, lean_object* v_k_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v_k_1377_; uint8_t v_strict_1378_; lean_object* v___y_1380_; 
v_k_1377_ = lean_ctor_get(v_k_1358_, 0);
v_strict_1378_ = lean_ctor_get_uint8(v_k_1358_, sizeof(void*)*1);
if (v_strict_1378_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1));
v___y_1380_ = v___x_1394_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3));
v___y_1380_ = v___x_1395_;
goto v___jp_1379_;
}
v___jp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = l_Lean_eagerReflBoolTrue;
v___x_1375_ = l_Lean_mkApp3(v___y_1372_, v_u_1357_, v___y_1373_, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
v___jp_1379_:
{
lean_object* v___x_1381_; 
lean_inc(v___y_1380_);
v___x_1381_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1380_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1384_ = lean_int_dec_le(v___x_1383_, v_k_1377_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1388_ = lean_int_neg(v_k_1377_);
v___x_1389_ = l_Int_toNat(v___x_1388_);
lean_dec(v___x_1388_);
v___x_1390_ = l_Lean_instToExprInt_mkNat(v___x_1389_);
v___x_1391_ = l_Lean_mkApp3(v___x_1385_, v___x_1386_, v___x_1387_, v___x_1390_);
v___y_1372_ = v_a_1382_;
v___y_1373_ = v___x_1391_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = l_Int_toNat(v_k_1377_);
v___x_1393_ = l_Lean_instToExprInt_mkNat(v___x_1392_);
v___y_1372_ = v_a_1382_;
v___y_1373_ = v___x_1393_;
goto v___jp_1371_;
}
}
else
{
lean_dec_ref(v_u_1357_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(lean_object* v_u_1396_, lean_object* v_k_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1396_, v_k_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_k_1397_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(lean_object* v_u_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1));
v___x_1431_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_1430_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l_Lean_Expr_app___override(v_a_1432_, v_u_1417_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_dec_ref(v_u_1417_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___boxed(lean_object* v_u_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
return v_res_1454_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1457_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1));
v___x_1458_ = lean_unsigned_to_nat(4u);
v___x_1459_ = lean_unsigned_to_nat(188u);
v___x_1460_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0));
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1462_ = l_mkPanicMessageWithDecl(v___x_1461_, v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object* v_u_1463_, lean_object* v_k_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Meta_Grind_Order_isRing(v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; uint8_t v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_unbox(v_a_1478_);
lean_dec(v_a_1478_);
if (v___x_1479_ == 0)
{
uint8_t v_strict_1480_; 
v_strict_1480_ = lean_ctor_get_uint8(v_k_1464_, sizeof(void*)*1);
if (v_strict_1480_ == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_1463_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v_u_1463_);
v___x_1482_ = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2);
v___x_1483_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1482_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1483_;
}
}
else
{
lean_object* v___x_1484_; 
v___x_1484_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_1463_, v_k_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1484_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_u_1463_);
v_a_1485_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1477_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1477_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___boxed(lean_object* v_u_1493_, lean_object* v_k_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_u_1493_, v_k_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_k_1494_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(lean_object* v_msg_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_panic_fn_borrowed(v___x_1509_, v_msg_1508_);
return v___x_1510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1));
v___x_1514_ = lean_unsigned_to_nat(22u);
v___x_1515_ = lean_unsigned_to_nat(196u);
v___x_1516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0));
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1518_ = l_mkPanicMessageWithDecl(v___x_1517_, v___x_1516_, v___x_1515_, v___x_1514_, v___x_1513_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(lean_object* v_u_1537_, lean_object* v_v_1538_, lean_object* v_k_1539_, lean_object* v_huv_1540_, lean_object* v_k_x27_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___y_1555_; uint8_t v_strict_1566_; 
v_strict_1566_ = lean_ctor_get_uint8(v_k_x27_1541_, sizeof(void*)*1);
if (v_strict_1566_ == 0)
{
uint8_t v_strict_1567_; 
v_strict_1567_ = lean_ctor_get_uint8(v_k_1539_, sizeof(void*)*1);
if (v_strict_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2);
v___x_1569_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_1568_);
v___y_1555_ = v___x_1569_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4));
v___y_1555_ = v___x_1570_;
goto v___jp_1554_;
}
}
else
{
uint8_t v_strict_1571_; 
v_strict_1571_ = lean_ctor_get_uint8(v_k_1539_, sizeof(void*)*1);
if (v_strict_1571_ == 0)
{
lean_object* v___x_1572_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6));
v___y_1555_ = v___x_1572_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8));
v___y_1555_ = v___x_1573_;
goto v___jp_1554_;
}
}
v___jp_1554_:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___y_1555_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1565_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = l_Lean_mkApp3(v_a_1557_, v_u_1537_, v_v_1538_, v_huv_1540_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1561_);
v___x_1563_ = v___x_1559_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_dec_ref(v_huv_1540_);
lean_dec_ref(v_v_1538_);
lean_dec_ref(v_u_1537_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___boxed(lean_object** _args){
lean_object* v_u_1574_ = _args[0];
lean_object* v_v_1575_ = _args[1];
lean_object* v_k_1576_ = _args[2];
lean_object* v_huv_1577_ = _args[3];
lean_object* v_k_x27_1578_ = _args[4];
lean_object* v_a_1579_ = _args[5];
lean_object* v_a_1580_ = _args[6];
lean_object* v_a_1581_ = _args[7];
lean_object* v_a_1582_ = _args[8];
lean_object* v_a_1583_ = _args[9];
lean_object* v_a_1584_ = _args[10];
lean_object* v_a_1585_ = _args[11];
lean_object* v_a_1586_ = _args[12];
lean_object* v_a_1587_ = _args[13];
lean_object* v_a_1588_ = _args[14];
lean_object* v_a_1589_ = _args[15];
lean_object* v_a_1590_ = _args[16];
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1574_, v_v_1575_, v_k_1576_, v_huv_1577_, v_k_x27_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_k_x27_1578_);
lean_dec_ref(v_k_1576_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(lean_object* v_u_1616_, lean_object* v_v_1617_, lean_object* v_k_1618_, lean_object* v_huv_1619_, lean_object* v_k_x27_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v_k_1640_; uint8_t v_strict_1641_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1657_; 
v_k_1640_ = lean_ctor_get(v_k_x27_1620_, 0);
v_strict_1641_ = lean_ctor_get_uint8(v_k_x27_1620_, sizeof(void*)*1);
if (v_strict_1641_ == 0)
{
uint8_t v_strict_1672_; 
v_strict_1672_ = lean_ctor_get_uint8(v_k_1618_, sizeof(void*)*1);
if (v_strict_1672_ == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1));
v___y_1657_ = v___x_1673_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3));
v___y_1657_ = v___x_1674_;
goto v___jp_1656_;
}
}
else
{
uint8_t v_strict_1675_; 
v_strict_1675_ = lean_ctor_get_uint8(v_k_1618_, sizeof(void*)*1);
if (v_strict_1675_ == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5));
v___y_1657_ = v___x_1676_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7));
v___y_1657_ = v___x_1677_;
goto v___jp_1656_;
}
}
v___jp_1633_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = l_Lean_eagerReflBoolTrue;
v___x_1638_ = l_Lean_mkApp6(v___y_1635_, v_u_1616_, v_v_1617_, v___y_1634_, v___y_1636_, v___x_1637_, v_huv_1619_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
v___jp_1642_:
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1646_ = lean_int_dec_le(v___x_1645_, v_k_1640_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1650_ = lean_int_neg(v_k_1640_);
v___x_1651_ = l_Int_toNat(v___x_1650_);
lean_dec(v___x_1650_);
v___x_1652_ = l_Lean_instToExprInt_mkNat(v___x_1651_);
v___x_1653_ = l_Lean_mkApp3(v___x_1647_, v___x_1648_, v___x_1649_, v___x_1652_);
v___y_1634_ = v___y_1644_;
v___y_1635_ = v___y_1643_;
v___y_1636_ = v___x_1653_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = l_Int_toNat(v_k_1640_);
v___x_1655_ = l_Lean_instToExprInt_mkNat(v___x_1654_);
v___y_1634_ = v___y_1644_;
v___y_1635_ = v___y_1643_;
v___y_1636_ = v___x_1655_;
goto v___jp_1633_;
}
}
v___jp_1656_:
{
lean_object* v___x_1658_; 
lean_inc(v___y_1657_);
v___x_1658_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1657_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_k_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_k_1660_ = lean_ctor_get(v_k_1618_, 0);
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1662_ = lean_int_dec_le(v___x_1661_, v_k_1660_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1666_ = lean_int_neg(v_k_1660_);
v___x_1667_ = l_Int_toNat(v___x_1666_);
lean_dec(v___x_1666_);
v___x_1668_ = l_Lean_instToExprInt_mkNat(v___x_1667_);
v___x_1669_ = l_Lean_mkApp3(v___x_1663_, v___x_1664_, v___x_1665_, v___x_1668_);
v___y_1643_ = v_a_1659_;
v___y_1644_ = v___x_1669_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = l_Int_toNat(v_k_1660_);
v___x_1671_ = l_Lean_instToExprInt_mkNat(v___x_1670_);
v___y_1643_ = v_a_1659_;
v___y_1644_ = v___x_1671_;
goto v___jp_1642_;
}
}
else
{
lean_dec_ref(v_huv_1619_);
lean_dec_ref(v_v_1617_);
lean_dec_ref(v_u_1616_);
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(lean_object** _args){
lean_object* v_u_1678_ = _args[0];
lean_object* v_v_1679_ = _args[1];
lean_object* v_k_1680_ = _args[2];
lean_object* v_huv_1681_ = _args[3];
lean_object* v_k_x27_1682_ = _args[4];
lean_object* v_a_1683_ = _args[5];
lean_object* v_a_1684_ = _args[6];
lean_object* v_a_1685_ = _args[7];
lean_object* v_a_1686_ = _args[8];
lean_object* v_a_1687_ = _args[9];
lean_object* v_a_1688_ = _args[10];
lean_object* v_a_1689_ = _args[11];
lean_object* v_a_1690_ = _args[12];
lean_object* v_a_1691_ = _args[13];
lean_object* v_a_1692_ = _args[14];
lean_object* v_a_1693_ = _args[15];
lean_object* v_a_1694_ = _args[16];
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1678_, v_v_1679_, v_k_1680_, v_huv_1681_, v_k_x27_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_k_x27_1682_);
lean_dec_ref(v_k_1680_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object* v_u_1696_, lean_object* v_v_1697_, lean_object* v_k_1698_, lean_object* v_huv_1699_, lean_object* v_k_x27_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Meta_Grind_Order_isRing(v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; uint8_t v___x_1715_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = lean_unbox(v_a_1714_);
lean_dec(v_a_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_1696_, v_v_1697_, v_k_1698_, v_huv_1699_, v_k_x27_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_1696_, v_v_1697_, v_k_1698_, v_huv_1699_, v_k_x27_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1717_;
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_huv_1699_);
lean_dec_ref(v_v_1697_);
lean_dec_ref(v_u_1696_);
v_a_1718_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1713_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof___boxed(lean_object** _args){
lean_object* v_u_1726_ = _args[0];
lean_object* v_v_1727_ = _args[1];
lean_object* v_k_1728_ = _args[2];
lean_object* v_huv_1729_ = _args[3];
lean_object* v_k_x27_1730_ = _args[4];
lean_object* v_a_1731_ = _args[5];
lean_object* v_a_1732_ = _args[6];
lean_object* v_a_1733_ = _args[7];
lean_object* v_a_1734_ = _args[8];
lean_object* v_a_1735_ = _args[9];
lean_object* v_a_1736_ = _args[10];
lean_object* v_a_1737_ = _args[11];
lean_object* v_a_1738_ = _args[12];
lean_object* v_a_1739_ = _args[13];
lean_object* v_a_1740_ = _args[14];
lean_object* v_a_1741_ = _args[15];
lean_object* v_a_1742_ = _args[16];
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_u_1726_, v_v_1727_, v_k_1728_, v_huv_1729_, v_k_x27_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_k_x27_1730_);
lean_dec_ref(v_k_1728_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(lean_object* v_u_1756_, lean_object* v_k_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v_k_1776_; uint8_t v_strict_1777_; lean_object* v___y_1779_; 
v_k_1776_ = lean_ctor_get(v_k_1757_, 0);
v_strict_1777_ = lean_ctor_get_uint8(v_k_1757_, sizeof(void*)*1);
if (v_strict_1777_ == 0)
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1));
v___y_1779_ = v___x_1793_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3));
v___y_1779_ = v___x_1794_;
goto v___jp_1778_;
}
v___jp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = l_Lean_eagerReflBoolTrue;
v___x_1774_ = l_Lean_mkApp3(v___y_1771_, v_u_1756_, v___y_1772_, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
v___jp_1778_:
{
lean_object* v___x_1780_; 
lean_inc(v___y_1779_);
v___x_1780_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1779_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1783_ = lean_int_dec_le(v___x_1782_, v_k_1776_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1787_ = lean_int_neg(v_k_1776_);
v___x_1788_ = l_Int_toNat(v___x_1787_);
lean_dec(v___x_1787_);
v___x_1789_ = l_Lean_instToExprInt_mkNat(v___x_1788_);
v___x_1790_ = l_Lean_mkApp3(v___x_1784_, v___x_1785_, v___x_1786_, v___x_1789_);
v___y_1771_ = v_a_1781_;
v___y_1772_ = v___x_1790_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = l_Int_toNat(v_k_1776_);
v___x_1792_ = l_Lean_instToExprInt_mkNat(v___x_1791_);
v___y_1771_ = v_a_1781_;
v___y_1772_ = v___x_1792_;
goto v___jp_1770_;
}
}
else
{
lean_dec_ref(v_u_1756_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(lean_object* v_u_1795_, lean_object* v_k_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1795_, v_k_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_k_1796_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(lean_object* v_u_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1));
v___x_1830_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_1829_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = l_Lean_Expr_app___override(v_a_1831_, v_u_1816_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_dec_ref(v_u_1816_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___boxed(lean_object* v_u_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec(v_a_1841_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1856_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1));
v___x_1857_ = lean_unsigned_to_nat(4u);
v___x_1858_ = lean_unsigned_to_nat(241u);
v___x_1859_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0));
v___x_1860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_1861_ = l_mkPanicMessageWithDecl(v___x_1860_, v___x_1859_, v___x_1858_, v___x_1857_, v___x_1856_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object* v_u_1862_, lean_object* v_k_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_Grind_Order_isRing(v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; uint8_t v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = lean_unbox(v_a_1877_);
lean_dec(v_a_1877_);
if (v___x_1878_ == 0)
{
uint8_t v_strict_1879_; 
v_strict_1879_ = lean_ctor_get_uint8(v_k_1863_, sizeof(void*)*1);
if (v_strict_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec_ref(v_u_1862_);
v___x_1880_ = lean_obj_once(&l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2, &l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once, _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2);
v___x_1881_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_1880_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_1862_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1882_;
}
}
else
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_1862_, v_k_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1883_;
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_u_1862_);
v_a_1884_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1876_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___boxed(lean_object* v_u_1892_, lean_object* v_k_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_u_1892_, v_k_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_k_1893_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(lean_object* v_u_1913_, lean_object* v_h_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
v___x_1928_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_1927_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = l_Lean_mkAppB(v_a_1929_, v_u_1913_, v_h_1914_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_dec_ref(v_h_1914_);
lean_dec_ref(v_u_1913_);
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___boxed(lean_object* v_u_1938_, lean_object* v_h_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_1938_, v_h_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec(v_a_1940_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(lean_object* v_u_1965_, lean_object* v_k_1966_, lean_object* v_h_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v_k_1986_; uint8_t v_strict_1987_; lean_object* v___y_1989_; 
v_k_1986_ = lean_ctor_get(v_k_1966_, 0);
v_strict_1987_ = lean_ctor_get_uint8(v_k_1966_, sizeof(void*)*1);
if (v_strict_1987_ == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
v___y_1989_ = v___x_2003_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2004_; 
v___x_2004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
v___y_1989_ = v___x_2004_;
goto v___jp_1988_;
}
v___jp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = l_Lean_eagerReflBoolTrue;
v___x_1984_ = l_Lean_mkApp4(v___y_1981_, v_u_1965_, v___y_1982_, v___x_1983_, v_h_1967_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
v___jp_1988_:
{
lean_object* v___x_1990_; 
lean_inc(v___y_1989_);
v___x_1990_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_1989_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_1993_ = lean_int_dec_le(v___x_1992_, v_k_1986_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_1995_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_1996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_1997_ = lean_int_neg(v_k_1986_);
v___x_1998_ = l_Int_toNat(v___x_1997_);
lean_dec(v___x_1997_);
v___x_1999_ = l_Lean_instToExprInt_mkNat(v___x_1998_);
v___x_2000_ = l_Lean_mkApp3(v___x_1994_, v___x_1995_, v___x_1996_, v___x_1999_);
v___y_1981_ = v_a_1991_;
v___y_1982_ = v___x_2000_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = l_Int_toNat(v_k_1986_);
v___x_2002_ = l_Lean_instToExprInt_mkNat(v___x_2001_);
v___y_1981_ = v_a_1991_;
v___y_1982_ = v___x_2002_;
goto v___jp_1980_;
}
}
else
{
lean_dec_ref(v_h_1967_);
lean_dec_ref(v_u_1965_);
return v___x_1990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(lean_object* v_u_2005_, lean_object* v_k_2006_, lean_object* v_h_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_2005_, v_k_2006_, v_h_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_k_2006_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object* v_u_2021_, lean_object* v_k_2022_, lean_object* v_h_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_Meta_Grind_Order_isRing(v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; uint8_t v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = lean_unbox(v_a_2037_);
lean_dec(v_a_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_2021_, v_h_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_2021_, v_k_2022_, v_h_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2040_;
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_h_2023_);
lean_dec_ref(v_u_2021_);
v_a_2041_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2036_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2036_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof___boxed(lean_object* v_u_2049_, lean_object* v_k_2050_, lean_object* v_h_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_u_2049_, v_k_2050_, v_h_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_k_2050_);
return v_res_2064_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1));
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = lean_unsigned_to_nat(268u);
v___x_2070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0));
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0));
v___x_2072_ = l_mkPanicMessageWithDecl(v___x_2071_, v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(lean_object* v_u_2073_, lean_object* v_v_2074_, lean_object* v_k_u2081_2075_, lean_object* v_h_u2081_2076_, lean_object* v_k_u2082_2077_, lean_object* v_h_u2082_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
uint8_t v_strict_2091_; uint8_t v_strict_2092_; lean_object* v___x_2093_; 
v_strict_2091_ = lean_ctor_get_uint8(v_k_u2081_2075_, sizeof(void*)*1);
v_strict_2092_ = lean_ctor_get_uint8(v_k_u2082_2077_, sizeof(void*)*1);
lean_inc_ref_n(v_u_2073_, 2);
v___x_2093_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_2073_, v_v_2074_, v_u_2073_, v_strict_2091_, v_strict_2092_, v_h_u2081_2076_, v_h_u2082_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
if (v_strict_2091_ == 0)
{
if (v_strict_2092_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v_a_2094_);
lean_dec_ref(v_u_2073_);
v___x_2107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2);
v___x_2108_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_2107_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2108_;
}
else
{
goto v___jp_2095_;
}
}
else
{
goto v___jp_2095_;
}
v___jp_2095_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1));
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2096_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2106_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2106_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2106_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = l_Lean_mkAppB(v_a_2098_, v_u_2073_, v_a_2094_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2102_);
v___x_2104_ = v___x_2100_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
else
{
lean_dec(v_a_2094_);
lean_dec_ref(v_u_2073_);
return v___x_2097_;
}
}
}
else
{
lean_dec_ref(v_u_2073_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___boxed(lean_object** _args){
lean_object* v_u_2109_ = _args[0];
lean_object* v_v_2110_ = _args[1];
lean_object* v_k_u2081_2111_ = _args[2];
lean_object* v_h_u2081_2112_ = _args[3];
lean_object* v_k_u2082_2113_ = _args[4];
lean_object* v_h_u2082_2114_ = _args[5];
lean_object* v_a_2115_ = _args[6];
lean_object* v_a_2116_ = _args[7];
lean_object* v_a_2117_ = _args[8];
lean_object* v_a_2118_ = _args[9];
lean_object* v_a_2119_ = _args[10];
lean_object* v_a_2120_ = _args[11];
lean_object* v_a_2121_ = _args[12];
lean_object* v_a_2122_ = _args[13];
lean_object* v_a_2123_ = _args[14];
lean_object* v_a_2124_ = _args[15];
lean_object* v_a_2125_ = _args[16];
lean_object* v_a_2126_ = _args[17];
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_2109_, v_v_2110_, v_k_u2081_2111_, v_h_u2081_2112_, v_k_u2082_2113_, v_h_u2082_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_k_u2082_2113_);
lean_dec_ref(v_k_u2081_2111_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(lean_object* v_u_2128_, lean_object* v_v_2129_, lean_object* v_k_u2081_2130_, lean_object* v_h_u2081_2131_, lean_object* v_k_u2082_2132_, lean_object* v_h_u2082_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v___x_2146_; 
lean_inc_ref_n(v_u_2128_, 2);
v___x_2146_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_2128_, v_v_2129_, v_u_2128_, v_k_u2081_2130_, v_k_u2082_2132_, v_h_u2081_2131_, v_h_u2082_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2182_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2182_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2182_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v_k_2159_; uint8_t v_strict_2160_; lean_object* v___y_2162_; 
v_k_2159_ = lean_ctor_get(v_k_u2081_2130_, 0);
v_strict_2160_ = lean_ctor_get_uint8(v_k_u2081_2130_, sizeof(void*)*1);
if (v_strict_2160_ == 0)
{
uint8_t v_strict_2180_; 
v_strict_2180_ = lean_ctor_get_uint8(v_k_u2082_2132_, sizeof(void*)*1);
if (v_strict_2180_ == 0)
{
lean_object* v___x_2181_; 
v___x_2181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1));
v___y_2162_ = v___x_2181_;
goto v___jp_2161_;
}
else
{
goto v___jp_2178_;
}
}
else
{
goto v___jp_2178_;
}
v___jp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2154_ = l_Lean_eagerReflBoolTrue;
v___x_2155_ = l_Lean_mkApp4(v___y_2152_, v_u_2128_, v___y_2153_, v___x_2154_, v_a_2147_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2155_);
v___x_2157_ = v___x_2149_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
v___jp_2161_:
{
lean_object* v___x_2163_; 
lean_inc(v___y_2162_);
v___x_2163_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___y_2162_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_k_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_k_2165_ = lean_ctor_get(v_k_u2082_2132_, 0);
v___x_2166_ = lean_int_add(v_k_2159_, v_k_2165_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
v___x_2168_ = lean_int_dec_le(v___x_2167_, v___x_2166_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
v___x_2172_ = lean_int_neg(v___x_2166_);
lean_dec(v___x_2166_);
v___x_2173_ = l_Int_toNat(v___x_2172_);
lean_dec(v___x_2172_);
v___x_2174_ = l_Lean_instToExprInt_mkNat(v___x_2173_);
v___x_2175_ = l_Lean_mkApp3(v___x_2169_, v___x_2170_, v___x_2171_, v___x_2174_);
v___y_2152_ = v_a_2164_;
v___y_2153_ = v___x_2175_;
goto v___jp_2151_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = l_Int_toNat(v___x_2166_);
lean_dec(v___x_2166_);
v___x_2177_ = l_Lean_instToExprInt_mkNat(v___x_2176_);
v___y_2152_ = v_a_2164_;
v___y_2153_ = v___x_2177_;
goto v___jp_2151_;
}
}
else
{
lean_del_object(v___x_2149_);
lean_dec(v_a_2147_);
lean_dec_ref(v_u_2128_);
return v___x_2163_;
}
}
v___jp_2178_:
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3));
v___y_2162_ = v___x_2179_;
goto v___jp_2161_;
}
}
}
else
{
lean_dec_ref(v_u_2128_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset___boxed(lean_object** _args){
lean_object* v_u_2183_ = _args[0];
lean_object* v_v_2184_ = _args[1];
lean_object* v_k_u2081_2185_ = _args[2];
lean_object* v_h_u2081_2186_ = _args[3];
lean_object* v_k_u2082_2187_ = _args[4];
lean_object* v_h_u2082_2188_ = _args[5];
lean_object* v_a_2189_ = _args[6];
lean_object* v_a_2190_ = _args[7];
lean_object* v_a_2191_ = _args[8];
lean_object* v_a_2192_ = _args[9];
lean_object* v_a_2193_ = _args[10];
lean_object* v_a_2194_ = _args[11];
lean_object* v_a_2195_ = _args[12];
lean_object* v_a_2196_ = _args[13];
lean_object* v_a_2197_ = _args[14];
lean_object* v_a_2198_ = _args[15];
lean_object* v_a_2199_ = _args[16];
lean_object* v_a_2200_ = _args[17];
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2183_, v_v_2184_, v_k_u2081_2185_, v_h_u2081_2186_, v_k_u2082_2187_, v_h_u2082_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_k_u2082_2187_);
lean_dec_ref(v_k_u2081_2185_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object* v_u_2202_, lean_object* v_v_2203_, lean_object* v_k_u2081_2204_, lean_object* v_h_u2081_2205_, lean_object* v_k_u2082_2206_, lean_object* v_h_u2082_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Meta_Grind_Order_isRing(v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; uint8_t v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2222_ = lean_unbox(v_a_2221_);
lean_dec(v_a_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_2202_, v_v_2203_, v_k_u2081_2204_, v_h_u2081_2205_, v_k_u2082_2206_, v_h_u2082_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_2202_, v_v_2203_, v_k_u2081_2204_, v_h_u2081_2205_, v_k_u2082_2206_, v_h_u2082_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2224_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_h_u2082_2207_);
lean_dec_ref(v_h_u2081_2205_);
lean_dec_ref(v_v_2203_);
lean_dec_ref(v_u_2202_);
v_a_2225_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2220_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2220_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof___boxed(lean_object** _args){
lean_object* v_u_2233_ = _args[0];
lean_object* v_v_2234_ = _args[1];
lean_object* v_k_u2081_2235_ = _args[2];
lean_object* v_h_u2081_2236_ = _args[3];
lean_object* v_k_u2082_2237_ = _args[4];
lean_object* v_h_u2082_2238_ = _args[5];
lean_object* v_a_2239_ = _args[6];
lean_object* v_a_2240_ = _args[7];
lean_object* v_a_2241_ = _args[8];
lean_object* v_a_2242_ = _args[9];
lean_object* v_a_2243_ = _args[10];
lean_object* v_a_2244_ = _args[11];
lean_object* v_a_2245_ = _args[12];
lean_object* v_a_2246_ = _args[13];
lean_object* v_a_2247_ = _args[14];
lean_object* v_a_2248_ = _args[15];
lean_object* v_a_2249_ = _args[16];
lean_object* v_a_2250_ = _args[17];
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_u_2233_, v_v_2234_, v_k_u2081_2235_, v_h_u2081_2236_, v_k_u2082_2237_, v_h_u2082_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_k_u2082_2237_);
lean_dec_ref(v_k_u2081_2235_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(lean_object* v_u_2258_, lean_object* v_v_2259_, lean_object* v_h_u2081_2260_, lean_object* v_h_u2082_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1));
v___x_2275_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_2274_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2284_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = l_Lean_mkApp4(v_a_2276_, v_u_2258_, v_v_2259_, v_h_u2081_2260_, v_h_u2082_2261_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_dec_ref(v_h_u2082_2261_);
lean_dec_ref(v_h_u2081_2260_);
lean_dec_ref(v_v_2259_);
lean_dec_ref(v_u_2258_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___boxed(lean_object* v_u_2285_, lean_object* v_v_2286_, lean_object* v_h_u2081_2287_, lean_object* v_h_u2082_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2285_, v_v_2286_, v_h_u2081_2287_, v_h_u2082_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec(v_a_2289_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(lean_object* v_u_2308_, lean_object* v_v_2309_, lean_object* v_h_u2081_2310_, lean_object* v_h_u2082_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_leCarrierIsSort(v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1));
v___x_2328_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_2327_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2346_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2346_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2346_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___y_2336_; lean_object* v_ringInst_x3f_2342_; 
v_ringInst_x3f_2342_ = lean_ctor_get(v_a_2331_, 10);
lean_inc(v_ringInst_x3f_2342_);
lean_dec(v_a_2331_);
if (lean_obj_tag(v_ringInst_x3f_2342_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_2344_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2343_);
v___y_2336_ = v___x_2344_;
goto v___jp_2335_;
}
else
{
lean_object* v_val_2345_; 
v_val_2345_ = lean_ctor_get(v_ringInst_x3f_2342_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v_ringInst_x3f_2342_, 1);
v___y_2336_ = v_val_2345_;
goto v___jp_2335_;
}
v___jp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = l_Lean_Expr_app___override(v_a_2329_, v___y_2336_);
v___x_2338_ = l_Lean_mkApp4(v___x_2337_, v_u_2308_, v_v_2309_, v_h_u2081_2310_, v_h_u2082_2311_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2338_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_a_2329_);
lean_dec_ref(v_h_u2082_2311_);
lean_dec_ref(v_h_u2081_2310_);
lean_dec_ref(v_v_2309_);
lean_dec_ref(v_u_2308_);
v_a_2347_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2330_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2330_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2082_2311_);
lean_dec_ref(v_h_u2081_2310_);
lean_dec_ref(v_v_2309_);
lean_dec_ref(v_u_2308_);
return v___x_2328_;
}
}
else
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v_type_2357_; lean_object* v_u_2358_; lean_object* v_leInst_2359_; lean_object* v_isPartialInst_x3f_2360_; lean_object* v_ringInst_x3f_2361_; lean_object* v___x_2362_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v_type_2357_ = lean_ctor_get(v_a_2356_, 1);
lean_inc_ref(v_type_2357_);
v_u_2358_ = lean_ctor_get(v_a_2356_, 2);
lean_inc(v_u_2358_);
v_leInst_2359_ = lean_ctor_get(v_a_2356_, 4);
lean_inc_ref(v_leInst_2359_);
v_isPartialInst_x3f_2360_ = lean_ctor_get(v_a_2356_, 6);
lean_inc(v_isPartialInst_x3f_2360_);
v_ringInst_x3f_2361_ = lean_ctor_get(v_a_2356_, 10);
lean_inc(v_ringInst_x3f_2361_);
lean_dec(v_a_2356_);
v___x_2362_ = l_Lean_Meta_decLevel(v_u_2358_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2388_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2388_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2388_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___y_2380_; 
v___x_2375_ = ((lean_object*)(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1));
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2363_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = l_Lean_mkConst(v___x_2375_, v___x_2377_);
if (lean_obj_tag(v_isPartialInst_x3f_2360_) == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_2386_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2385_);
v___y_2380_ = v___x_2386_;
goto v___jp_2379_;
}
else
{
lean_object* v_val_2387_; 
v_val_2387_ = lean_ctor_get(v_isPartialInst_x3f_2360_, 0);
lean_inc(v_val_2387_);
lean_dec_ref_known(v_isPartialInst_x3f_2360_, 1);
v___y_2380_ = v_val_2387_;
goto v___jp_2379_;
}
v___jp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2370_ = l_Lean_Expr_app___override(v___y_2368_, v___y_2369_);
v___x_2371_ = l_Lean_mkApp4(v___x_2370_, v_u_2308_, v_v_2309_, v_h_u2081_2310_, v_h_u2082_2311_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2371_);
v___x_2373_ = v___x_2365_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
v___jp_2379_:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_mkApp3(v___x_2378_, v_type_2357_, v_leInst_2359_, v___y_2380_);
if (lean_obj_tag(v_ringInst_x3f_2361_) == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
v___x_2383_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2382_);
v___y_2368_ = v___x_2381_;
v___y_2369_ = v___x_2383_;
goto v___jp_2367_;
}
else
{
lean_object* v_val_2384_; 
v_val_2384_ = lean_ctor_get(v_ringInst_x3f_2361_, 0);
lean_inc(v_val_2384_);
lean_dec_ref_known(v_ringInst_x3f_2361_, 1);
v___y_2368_ = v___x_2381_;
v___y_2369_ = v_val_2384_;
goto v___jp_2367_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_ringInst_x3f_2361_);
lean_dec(v_isPartialInst_x3f_2360_);
lean_dec_ref(v_leInst_2359_);
lean_dec_ref(v_type_2357_);
lean_dec_ref(v_h_u2082_2311_);
lean_dec_ref(v_h_u2081_2310_);
lean_dec_ref(v_v_2309_);
lean_dec_ref(v_u_2308_);
v_a_2389_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2362_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2362_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_h_u2082_2311_);
lean_dec_ref(v_h_u2081_2310_);
lean_dec_ref(v_v_2309_);
lean_dec_ref(v_u_2308_);
v_a_2397_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2355_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2355_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_h_u2082_2311_);
lean_dec_ref(v_h_u2081_2310_);
lean_dec_ref(v_v_2309_);
lean_dec_ref(v_u_2308_);
v_a_2405_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2324_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2324_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___boxed(lean_object* v_u_2413_, lean_object* v_v_2414_, lean_object* v_h_u2081_2415_, lean_object* v_h_u2082_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2413_, v_v_2414_, v_h_u2081_2415_, v_h_u2082_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec(v_a_2417_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object* v_u_2430_, lean_object* v_v_2431_, lean_object* v_h_u2081_2432_, lean_object* v_h_u2082_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Meta_Grind_Order_isRing(v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; uint8_t v___x_2448_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = lean_unbox(v_a_2447_);
lean_dec(v_a_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(v_u_2430_, v_v_2431_, v_h_u2081_2432_, v_h_u2082_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(v_u_2430_, v_v_2431_, v_h_u2081_2432_, v_h_u2082_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v___x_2450_;
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_h_u2082_2433_);
lean_dec_ref(v_h_u2081_2432_);
lean_dec_ref(v_v_2431_);
lean_dec_ref(v_u_2430_);
v_a_2451_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2446_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2446_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe___boxed(lean_object* v_u_2459_, lean_object* v_v_2460_, lean_object* v_h_u2081_2461_, lean_object* v_h_u2082_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_u_2459_, v_v_2460_, v_h_u2081_2461_, v_h_u2082_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec(v_a_2463_);
return v_res_2475_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
