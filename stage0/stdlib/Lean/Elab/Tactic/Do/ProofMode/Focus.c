// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Focus
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.MGoal
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_focusHyp_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Focus"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 57, 88, 170, 28, 205, 228, 3)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(217, 216, 169, 87, 101, 39, 91, 236)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 57, 88, 170, 28, 205, 228, 3)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(113, 125, 131, 44, 226, 252, 17, 219)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 57, 88, 170, 28, 205, 228, 3)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value),LEAN_SCALAR_PTR_LITERAL(23, 171, 227, 57, 23, 180, 164, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.Tactic.Do.ProofMode.Focus"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Elab.Tactic.Do.ProofMode.focusHyp"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "focusHyp: hypothesis without proper metadata: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bientails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 51, 221, 5, 242, 131, 169, 118)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 95, 37, 108, 69, 205, 235, 200)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_recombineGoal(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rewrite_hyps"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 57, 88, 170, 28, 205, 228, 3)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 118, 70, 222, 218, 9, 178, 199)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "impossible; res.focusHyp not a hypothesis"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown hypothesis `"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
lean_ctor_set(v___x_8_, 2, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default;
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_focusHyp_spec__0(lean_object* v_msg_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_box(0);
v___x_13_ = lean_panic_fn(v___x_12_, v_msg_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(lean_object* v_u_46_, lean_object* v_00_u03c3s_47_, lean_object* v_e_48_, lean_object* v_name_49_){
_start:
{
lean_object* v___x_50_; 
lean_inc_ref(v_e_48_);
v___x_50_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_48_);
if (lean_obj_tag(v___x_50_) == 1)
{
lean_object* v_val_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_76_; 
v_val_51_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_76_ == 0)
{
v___x_53_ = v___x_50_;
v_isShared_54_ = v_isSharedCheck_76_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_val_51_);
lean_dec(v___x_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_76_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_name_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_73_; 
v_name_55_ = lean_ctor_get(v_val_51_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_val_51_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; lean_object* v_unused_75_; 
v_unused_74_ = lean_ctor_get(v_val_51_, 2);
lean_dec(v_unused_74_);
v_unused_75_ = lean_ctor_get(v_val_51_, 1);
lean_dec(v_unused_75_);
v___x_57_ = v_val_51_;
v_isShared_58_ = v_isSharedCheck_73_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_name_55_);
lean_dec(v_val_51_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_73_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; 
v___x_59_ = lean_name_eq(v_name_55_, v_name_49_);
lean_dec(v_name_55_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_del_object(v___x_57_);
lean_del_object(v___x_53_);
lean_dec_ref(v_e_48_);
lean_dec_ref(v_00_u03c3s_47_);
lean_dec(v_u_46_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
lean_inc_ref(v_00_u03c3s_47_);
lean_inc(v_u_46_);
v___x_61_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_46_, v_00_u03c3s_47_);
v___x_62_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6));
v___x_63_ = lean_box(0);
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v_u_46_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = l_Lean_mkConst(v___x_62_, v___x_64_);
lean_inc_ref(v_e_48_);
v___x_66_ = l_Lean_mkAppB(v___x_65_, v_00_u03c3s_47_, v_e_48_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 2, v___x_66_);
lean_ctor_set(v___x_57_, 1, v___x_61_);
lean_ctor_set(v___x_57_, 0, v_e_48_);
v___x_68_ = v___x_57_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_e_48_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_72_, 2, v___x_66_);
v___x_68_ = v_reuseFailAlloc_72_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_70_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_68_);
v___x_70_ = v___x_53_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
}
else
{
lean_object* v___x_77_; 
lean_dec(v___x_50_);
lean_dec_ref(v_00_u03c3s_47_);
lean_dec(v_u_46_);
v___x_77_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_48_);
if (lean_obj_tag(v___x_77_) == 1)
{
lean_object* v_val_78_; lean_object* v_snd_79_; lean_object* v_snd_80_; lean_object* v_fst_81_; lean_object* v_fst_82_; lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_85_; 
lean_dec_ref(v_e_48_);
v_val_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_val_78_);
lean_dec_ref(v___x_77_);
v_snd_79_ = lean_ctor_get(v_val_78_, 1);
lean_inc(v_snd_79_);
v_snd_80_ = lean_ctor_get(v_snd_79_, 1);
lean_inc(v_snd_80_);
v_fst_81_ = lean_ctor_get(v_val_78_, 0);
lean_inc(v_fst_81_);
lean_dec(v_val_78_);
v_fst_82_ = lean_ctor_get(v_snd_79_, 0);
lean_inc(v_fst_82_);
lean_dec(v_snd_79_);
v_fst_83_ = lean_ctor_get(v_snd_80_, 0);
lean_inc(v_fst_83_);
v_snd_84_ = lean_ctor_get(v_snd_80_, 1);
lean_inc(v_snd_84_);
lean_dec(v_snd_80_);
lean_inc(v_snd_84_);
lean_inc(v_fst_82_);
lean_inc(v_fst_81_);
v___x_85_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_fst_81_, v_fst_82_, v_snd_84_, v_name_49_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v___x_86_; 
lean_inc(v_fst_83_);
lean_inc(v_fst_82_);
lean_inc(v_fst_81_);
v___x_86_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_fst_81_, v_fst_82_, v_fst_83_, v_name_49_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_dec(v_snd_84_);
lean_dec(v_fst_83_);
lean_dec(v_fst_82_);
lean_dec(v_fst_81_);
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_118_; 
v_val_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_118_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_118_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_val_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_118_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_focusHyp_91_; lean_object* v_restHyps_92_; lean_object* v_proof_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_117_; 
v_focusHyp_91_ = lean_ctor_get(v_val_87_, 0);
v_restHyps_92_ = lean_ctor_get(v_val_87_, 1);
v_proof_93_ = lean_ctor_get(v_val_87_, 2);
v_isSharedCheck_117_ = !lean_is_exclusive(v_val_87_);
if (v_isSharedCheck_117_ == 0)
{
v___x_95_ = v_val_87_;
v_isShared_96_ = v_isSharedCheck_117_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_proof_93_);
lean_inc(v_restHyps_92_);
lean_inc(v_focusHyp_91_);
lean_dec(v_val_87_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_117_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_snd_84_);
lean_inc_ref(v_restHyps_92_);
lean_inc(v_fst_82_);
lean_inc(v_fst_81_);
v___x_97_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_fst_81_, v_fst_82_, v_restHyps_92_, v_snd_84_);
v_fst_98_ = lean_ctor_get(v___x_97_, 0);
v_snd_99_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_116_ == 0)
{
v___x_101_ = v___x_97_;
v_isShared_102_ = v_isSharedCheck_116_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_snd_99_);
lean_inc(v_fst_98_);
lean_dec(v___x_97_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_116_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8));
v___x_104_ = lean_box(0);
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 1);
lean_ctor_set(v___x_101_, 1, v___x_104_);
lean_ctor_set(v___x_101_, 0, v_fst_81_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_fst_81_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_115_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = l_Lean_mkConst(v___x_103_, v___x_106_);
lean_inc_ref(v_focusHyp_91_);
lean_inc(v_fst_98_);
v___x_108_ = l_Lean_mkApp8(v___x_107_, v_fst_82_, v_fst_83_, v_restHyps_92_, v_snd_84_, v_fst_98_, v_focusHyp_91_, v_proof_93_, v_snd_99_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 2, v___x_108_);
lean_ctor_set(v___x_95_, 1, v_fst_98_);
v___x_110_ = v___x_95_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_focusHyp_91_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_fst_98_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v___x_108_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_110_);
v___x_112_ = v___x_89_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
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
lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_150_; 
v_val_119_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_150_ == 0)
{
v___x_121_ = v___x_85_;
v_isShared_122_ = v_isSharedCheck_150_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_dec(v___x_85_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_150_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_focusHyp_123_; lean_object* v_restHyps_124_; lean_object* v_proof_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_149_; 
v_focusHyp_123_ = lean_ctor_get(v_val_119_, 0);
v_restHyps_124_ = lean_ctor_get(v_val_119_, 1);
v_proof_125_ = lean_ctor_get(v_val_119_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v_val_119_);
if (v_isSharedCheck_149_ == 0)
{
v___x_127_ = v_val_119_;
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_proof_125_);
lean_inc(v_restHyps_124_);
lean_inc(v_focusHyp_123_);
lean_dec(v_val_119_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_148_; 
lean_inc_ref(v_restHyps_124_);
lean_inc(v_fst_83_);
lean_inc(v_fst_82_);
lean_inc(v_fst_81_);
v___x_129_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_fst_81_, v_fst_82_, v_fst_83_, v_restHyps_124_);
v_fst_130_ = lean_ctor_get(v___x_129_, 0);
v_snd_131_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_148_ == 0)
{
v___x_133_ = v___x_129_;
v_isShared_134_ = v_isSharedCheck_148_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_snd_131_);
lean_inc(v_fst_130_);
lean_dec(v___x_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_148_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10));
v___x_136_ = lean_box(0);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 1);
lean_ctor_set(v___x_133_, 1, v___x_136_);
lean_ctor_set(v___x_133_, 0, v_fst_81_);
v___x_138_ = v___x_133_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_81_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_147_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_139_ = l_Lean_mkConst(v___x_135_, v___x_138_);
lean_inc_ref(v_focusHyp_123_);
lean_inc(v_fst_130_);
v___x_140_ = l_Lean_mkApp8(v___x_139_, v_fst_82_, v_fst_83_, v_snd_84_, v_restHyps_124_, v_fst_130_, v_focusHyp_123_, v_proof_125_, v_snd_131_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 2, v___x_140_);
lean_ctor_set(v___x_127_, 1, v_fst_130_);
v___x_142_ = v___x_127_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_focusHyp_123_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_fst_130_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v___x_140_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_142_);
v___x_144_ = v___x_121_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
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
lean_object* v___x_151_; 
lean_dec(v___x_77_);
lean_inc_ref(v_e_48_);
v___x_151_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_48_);
if (lean_obj_tag(v___x_151_) == 1)
{
lean_object* v___x_152_; 
lean_dec_ref(v___x_151_);
lean_dec_ref(v_e_48_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v___x_151_);
v___x_153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11));
v___x_154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12));
v___x_155_ = lean_unsigned_to_nat(46u);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13));
v___x_158_ = lean_expr_dbg_to_string(v_e_48_);
lean_dec_ref(v_e_48_);
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l_mkPanicMessageWithDecl(v___x_153_, v___x_154_, v___x_155_, v___x_156_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_focusHyp_spec__0(v___x_160_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___boxed(lean_object* v_u_162_, lean_object* v_00_u03c3s_163_, lean_object* v_e_164_, lean_object* v_name_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_u_162_, v_00_u03c3s_163_, v_e_164_, v_name_165_);
lean_dec(v_name_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(lean_object* v_goal_167_, lean_object* v_name_168_){
_start:
{
lean_object* v_u_169_; lean_object* v_00_u03c3s_170_; lean_object* v_hyps_171_; lean_object* v___x_172_; 
v_u_169_ = lean_ctor_get(v_goal_167_, 0);
lean_inc(v_u_169_);
v_00_u03c3s_170_ = lean_ctor_get(v_goal_167_, 1);
lean_inc_ref(v_00_u03c3s_170_);
v_hyps_171_ = lean_ctor_get(v_goal_167_, 2);
lean_inc_ref(v_hyps_171_);
lean_dec_ref(v_goal_167_);
v___x_172_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_u_169_, v_00_u03c3s_170_, v_hyps_171_, v_name_168_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp___boxed(lean_object* v_goal_173_, lean_object* v_name_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_goal_173_, v_name_174_);
lean_dec(v_name_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl(lean_object* v_u_184_, lean_object* v_00_u03c3s_185_, lean_object* v_restHyps_186_, lean_object* v_focusHyp_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_proof_193_; lean_object* v___x_194_; 
v___x_188_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2));
v___x_189_ = lean_box(0);
lean_inc(v_u_184_);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v_u_184_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = l_Lean_mkConst(v___x_188_, v___x_190_);
lean_inc_ref(v_focusHyp_187_);
lean_inc_ref(v_restHyps_186_);
lean_inc_ref(v_00_u03c3s_185_);
v___x_192_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_184_, v_00_u03c3s_185_, v_restHyps_186_, v_focusHyp_187_);
v_proof_193_ = l_Lean_mkAppB(v___x_191_, v_00_u03c3s_185_, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_194_, 0, v_focusHyp_187_);
lean_ctor_set(v___x_194_, 1, v_restHyps_186_);
lean_ctor_set(v___x_194_, 2, v_proof_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(lean_object* v_res_195_, lean_object* v_goal_196_){
_start:
{
lean_object* v_u_197_; lean_object* v_00_u03c3s_198_; lean_object* v_target_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_u_197_ = lean_ctor_get(v_goal_196_, 0);
v_00_u03c3s_198_ = lean_ctor_get(v_goal_196_, 1);
v_target_199_ = lean_ctor_get(v_goal_196_, 3);
v_isSharedCheck_207_ = !lean_is_exclusive(v_goal_196_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_goal_196_, 2);
lean_dec(v_unused_208_);
v___x_201_ = v_goal_196_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_target_199_);
lean_inc(v_00_u03c3s_198_);
lean_inc(v_u_197_);
lean_dec(v_goal_196_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_restHyps_203_; lean_object* v___x_205_; 
v_restHyps_203_ = lean_ctor_get(v_res_195_, 1);
lean_inc_ref(v_restHyps_203_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 2, v_restHyps_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_u_197_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_00_u03c3s_198_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_restHyps_203_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_target_199_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal___boxed(lean_object* v_res_209_, lean_object* v_goal_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_res_209_, v_goal_210_);
lean_dec_ref(v_res_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_recombineGoal(lean_object* v_res_212_, lean_object* v_goal_213_){
_start:
{
lean_object* v_u_214_; lean_object* v_00_u03c3s_215_; lean_object* v_target_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_226_; 
v_u_214_ = lean_ctor_get(v_goal_213_, 0);
v_00_u03c3s_215_ = lean_ctor_get(v_goal_213_, 1);
v_target_216_ = lean_ctor_get(v_goal_213_, 3);
v_isSharedCheck_226_ = !lean_is_exclusive(v_goal_213_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v_goal_213_, 2);
lean_dec(v_unused_227_);
v___x_218_ = v_goal_213_;
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_target_216_);
lean_inc(v_00_u03c3s_215_);
lean_inc(v_u_214_);
lean_dec(v_goal_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_focusHyp_220_; lean_object* v_restHyps_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v_focusHyp_220_ = lean_ctor_get(v_res_212_, 0);
lean_inc_ref(v_focusHyp_220_);
v_restHyps_221_ = lean_ctor_get(v_res_212_, 1);
lean_inc_ref(v_restHyps_221_);
lean_dec_ref(v_res_212_);
lean_inc_ref(v_00_u03c3s_215_);
lean_inc(v_u_214_);
v___x_222_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_214_, v_00_u03c3s_215_, v_restHyps_221_, v_focusHyp_220_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 2, v___x_222_);
v___x_224_ = v___x_218_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_u_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_00_u03c3s_215_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_target_216_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(lean_object* v_res_236_, lean_object* v_goal_237_, lean_object* v_e_u2082_238_){
_start:
{
lean_object* v_u_239_; lean_object* v_00_u03c3s_240_; lean_object* v_hyps_241_; lean_object* v_target_242_; lean_object* v_focusHyp_243_; lean_object* v_restHyps_244_; lean_object* v_proof_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_u_239_ = lean_ctor_get(v_goal_237_, 0);
lean_inc(v_u_239_);
v_00_u03c3s_240_ = lean_ctor_get(v_goal_237_, 1);
lean_inc_ref(v_00_u03c3s_240_);
v_hyps_241_ = lean_ctor_get(v_goal_237_, 2);
lean_inc_ref(v_hyps_241_);
v_target_242_ = lean_ctor_get(v_goal_237_, 3);
lean_inc_ref(v_target_242_);
lean_dec_ref(v_goal_237_);
v_focusHyp_243_ = lean_ctor_get(v_res_236_, 0);
lean_inc_ref(v_focusHyp_243_);
v_restHyps_244_ = lean_ctor_get(v_res_236_, 1);
lean_inc_ref(v_restHyps_244_);
v_proof_245_ = lean_ctor_get(v_res_236_, 2);
lean_inc_ref(v_proof_245_);
lean_dec_ref(v_res_236_);
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1));
v___x_247_ = lean_box(0);
lean_inc(v_u_239_);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v_u_239_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_mkConst(v___x_246_, v___x_248_);
lean_inc_ref(v_00_u03c3s_240_);
v___x_250_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_239_, v_00_u03c3s_240_, v_restHyps_244_, v_focusHyp_243_);
v___x_251_ = l_Lean_mkApp6(v___x_249_, v_00_u03c3s_240_, v_hyps_241_, v___x_250_, v_target_242_, v_proof_245_, v_e_u2082_238_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(lean_object* v_msgData_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_env_259_; lean_object* v___x_260_; lean_object* v_mctx_261_; lean_object* v_lctx_262_; lean_object* v_options_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_258_ = lean_st_ref_get(v___y_256_);
v_env_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_258_);
v___x_260_ = lean_st_ref_get(v___y_254_);
v_mctx_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_mctx_261_);
lean_dec(v___x_260_);
v_lctx_262_ = lean_ctor_get(v___y_253_, 2);
v_options_263_ = lean_ctor_get(v___y_255_, 2);
lean_inc_ref(v_options_263_);
lean_inc_ref(v_lctx_262_);
v___x_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_264_, 0, v_env_259_);
lean_ctor_set(v___x_264_, 1, v_mctx_261_);
lean_ctor_set(v___x_264_, 2, v_lctx_262_);
lean_ctor_set(v___x_264_, 3, v_options_263_);
v___x_265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_msgData_252_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0___boxed(lean_object* v_msgData_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(v_msgData_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_ref_280_; lean_object* v___x_281_; lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_ref_280_ = lean_ctor_get(v___y_277_, 5);
v___x_281_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
lean_inc(v_ref_280_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_ref_280_);
lean_ctor_set(v___x_286_, 1, v_a_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set_tag(v___x_284_, 1);
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg___boxed(lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v_msg_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object* v_goal_307_, lean_object* v_name_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l_Lean_TSyntax_getId(v_name_308_);
lean_inc_ref(v_goal_307_);
v___x_315_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_goal_307_, v___x_314_);
lean_dec(v___x_314_);
if (lean_obj_tag(v___x_315_) == 1)
{
lean_object* v_val_316_; lean_object* v_focusHyp_317_; lean_object* v___x_318_; 
v_val_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_316_);
lean_dec_ref(v___x_315_);
v_focusHyp_317_ = lean_ctor_get(v_val_316_, 0);
lean_inc_ref(v_focusHyp_317_);
v___x_318_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_317_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; lean_object* v_00_u03c3s_320_; uint8_t v___x_321_; lean_object* v___x_322_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_319_);
lean_dec_ref(v___x_318_);
v_00_u03c3s_320_ = lean_ctor_get(v_goal_307_, 1);
lean_inc_ref(v_00_u03c3s_320_);
lean_dec_ref(v_goal_307_);
v___x_321_ = 0;
v___x_322_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_name_308_, v_00_u03c3s_320_, v_val_319_, v___x_321_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_330_);
v___x_324_ = v___x_322_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_dec(v___x_322_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_val_316_);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_val_316_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_val_316_);
v_a_331_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_322_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_322_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v___x_318_);
lean_dec(v_val_316_);
lean_dec(v_name_308_);
lean_dec_ref(v_goal_307_);
v___x_339_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1);
v___x_340_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v___x_339_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v___x_340_;
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v___x_315_);
lean_dec_ref(v_goal_307_);
v___x_341_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3);
v___x_342_ = l_Lean_MessageData_ofSyntax(v_name_308_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v___x_345_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed(lean_object* v_goal_347_, lean_object* v_name_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_347_, v_name_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(lean_object* v_00_u03b1_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v_msg_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___boxed(lean_object* v_00_u03b1_363_, lean_object* v_msg_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(v_00_u03b1_363_, v_msg_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default = _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default);
l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult = _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
}
#ifdef __cplusplus
}
#endif
