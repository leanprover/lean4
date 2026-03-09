// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: public import Init.Grind.Propagator import Init.Simproc import Init.Grind.Norm import Lean.Meta.Tactic.Grind.Internalize import Lean.Meta.Tactic.Grind.Anchor import Lean.Meta.Tactic.Grind.EqResolution import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.PropagatorAttr import Init.Grind.Lemmas
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_false_of_imp_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 135, 203, 106, 42, 89, 33, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "imp_eq_of_eq_true_right"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 104, 37, 206, 110, 37, 230, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "imp_eq_of_eq_true_left"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(71, 219, 112, 102, 237, 48, 138, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "imp_eq_of_eq_false_left"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(71, 59, 221, 124, 3, 234, 184, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "forall_propagator"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 98, 167, 92, 43, 63, 200, 147)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forallPropagator"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(62, 20, 227, 217, 136, 128, 93, 131)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "q': "};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__7_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " for"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isEqTrue, "};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 213, 255, 45, 151, 209, 83, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0_value;
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to create E-match local theorem for"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value),LEAN_SCALAR_PTR_LITERAL(120, 104, 189, 185, 38, 81, 44, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "eqResolution"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 23, 253, 34, 8, 106, 124, 207)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_forall_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value),LEAN_SCALAR_PTR_LITERAL(173, 140, 239, 244, 206, 215, 220, 192)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_true_of_imp_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 202, 44, 200, 3, 215, 155, 153)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_false_of_imp_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__11_value),LEAN_SCALAR_PTR_LITERAL(224, 133, 152, 168, 210, 40, 234, 100)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateExistsDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateExistsDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateExistsDown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__2;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_propagateExistsDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__3;
static const lean_string_object l_Lean_Meta_Grind_propagateExistsDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateExistsDown___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_propagateExistsDown___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "forall_not_of_not_exists"};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateExistsDown___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__6_value),LEAN_SCALAR_PTR_LITERAL(64, 176, 52, 188, 216, 118, 163, 15)}};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__7_value;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "forall_and"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__5_value),LEAN_SCALAR_PTR_LITERAL(81, 10, 210, 75, 235, 208, 8, 129)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_forall_or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 112, 166, 94, 237, 48, 167, 129)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_or_forall"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 14, 212, 131, 198, 226, 199, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__13;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_self_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value),LEAN_SCALAR_PTR_LITERAL(166, 96, 8, 70, 216, 37, 74, 175)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__16;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_imp_eq_or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value),LEAN_SCALAR_PTR_LITERAL(61, 240, 249, 78, 172, 240, 254, 86)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_true_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value),LEAN_SCALAR_PTR_LITERAL(23, 129, 235, 110, 107, 55, 234, 42)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__21;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_false_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value),LEAN_SCALAR_PTR_LITERAL(217, 93, 174, 85, 201, 7, 0, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__24;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "true_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value),LEAN_SCALAR_PTR_LITERAL(20, 154, 121, 57, 70, 129, 111, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__27;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "false_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value),LEAN_SCALAR_PTR_LITERAL(127, 143, 249, 102, 140, 8, 231, 12)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__30;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__31_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__32_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__33;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_true"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__34_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 84, 112, 33, 203, 156, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__35_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__36;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__37;
lean_object* l_Lean_mkSort(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__38;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_false"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__39_value),LEAN_SCALAR_PTR_LITERAL(12, 96, 31, 202, 138, 131, 44, 134)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__40_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__41;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpForall"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(207, 161, 230, 164, 57, 132, 181, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "exists_const"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 209, 190, 134, 241, 243, 173, 71)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exists_prop"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 14, 159, 153, 168, 50, 182, 0)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpExists___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "exists_and_right"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 93, 78, 251, 76, 254, 187, 237)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exists_and_left"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 136, 99, 9, 218, 202, 25, 69)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exists_or"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(161, 112, 226, 203, 229, 162, 152, 185)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value;
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpExists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(220, 43, 168, 20, 165, 143, 80, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_58; uint8_t x_90; lean_object* x_91; lean_object* x_120; lean_object* x_152; 
x_152 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_3, x_4);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_166; 
x_153 = lean_ctor_get(x_152, 0);
x_166 = !lean_is_exclusive(x_152);
if (x_166 == 0)
{
x_154 = x_152;
x_155 = x_166;
goto block_165;
}
else
{
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_box(0);
x_155 = x_166;
goto block_165;
}
block_165:
{
uint8_t x_156; 
x_156 = lean_unbox(x_153);
lean_dec(x_153);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_157 = lean_box(0);
if (x_155 == 0)
{
lean_ctor_set(x_154, 0, x_157);
x_158 = x_154;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_157);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
else
{
lean_object* x_161; 
lean_del_object(x_154);
lean_inc_ref(x_2);
x_161 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
x_120 = x_161;
goto block_151;
}
else
{
lean_object* x_164; 
lean_dec_ref(x_161);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_3);
x_164 = l_Lean_Meta_isProp(x_3, x_10, x_11, x_12, x_13);
x_120 = x_164;
goto block_151;
}
}
else
{
x_120 = x_161;
goto block_151;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_174; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = lean_ctor_get(x_152, 0);
x_174 = !lean_is_exclusive(x_152);
if (x_174 == 0)
{
x_168 = x_152;
x_169 = x_174;
goto block_173;
}
else
{
lean_inc(x_167);
lean_dec(x_152);
x_168 = lean_box(0);
x_169 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_170; 
if (x_169 == 0)
{
x_170 = x_168;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_170 = x_172;
goto block_171;
}
block_171:
{
return x_170;
}
}
}
block_57:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_48; 
x_16 = lean_ctor_get(x_15, 0);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
x_17 = x_15;
x_18 = x_48;
goto block_47;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_48;
goto block_47;
}
block_47:
{
uint8_t x_19; 
x_19 = lean_unbox(x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
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
lean_object* x_24; 
lean_del_object(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_26 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(x_2);
x_29 = l_Lean_mkApp4(x_28, x_2, x_3, x_25, x_27);
x_30 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_29, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_26, 0);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
x_32 = x_26;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_26);
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
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
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
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_24, 0);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
x_40 = x_24;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_15, 0);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
x_50 = x_15;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
block_89:
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_inc_ref(x_3);
x_61 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
x_15 = x_61;
goto block_57;
}
else
{
lean_object* x_64; 
lean_dec_ref(x_61);
lean_inc_ref(x_1);
x_64 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
x_15 = x_64;
goto block_57;
}
else
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_2);
x_67 = l_Lean_Meta_isProp(x_2, x_10, x_11, x_12, x_13);
x_15 = x_67;
goto block_57;
}
}
else
{
x_15 = x_64;
goto block_57;
}
}
}
else
{
x_15 = x_61;
goto block_57;
}
}
else
{
lean_object* x_68; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_68 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7);
x_71 = l_Lean_mkApp3(x_70, x_2, x_3, x_69);
x_72 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_71, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_68, 0);
x_80 = !lean_is_exclusive(x_68);
if (x_80 == 0)
{
x_74 = x_68;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_58, 0);
x_88 = !lean_is_exclusive(x_58);
if (x_88 == 0)
{
x_82 = x_58;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_58);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
block_119:
{
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_inc_ref(x_3);
x_94 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
x_58 = x_94;
goto block_89;
}
else
{
lean_object* x_97; 
lean_dec_ref(x_94);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_2);
x_97 = l_Lean_Meta_isProp(x_2, x_10, x_11, x_12, x_13);
x_58 = x_97;
goto block_89;
}
}
else
{
x_58 = x_94;
goto block_89;
}
}
else
{
lean_object* x_98; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_98 = l_Lean_Meta_Grind_mkEqTrueProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10);
lean_inc_ref(x_3);
x_101 = l_Lean_mkApp3(x_100, x_2, x_3, x_99);
x_102 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_3, x_101, x_90, x_4, x_6, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_98, 0);
x_110 = !lean_is_exclusive(x_98);
if (x_110 == 0)
{
x_104 = x_98;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
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
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_91, 0);
x_118 = !lean_is_exclusive(x_91);
if (x_118 == 0)
{
x_112 = x_91;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_91);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
block_151:
{
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_inc_ref(x_2);
x_123 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = lean_unbox(x_121);
lean_dec(x_121);
x_90 = x_126;
x_91 = x_123;
goto block_119;
}
else
{
lean_object* x_127; uint8_t x_128; 
lean_dec_ref(x_123);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_3);
x_127 = l_Lean_Meta_isProp(x_3, x_10, x_11, x_12, x_13);
x_128 = lean_unbox(x_121);
lean_dec(x_121);
x_90 = x_128;
x_91 = x_127;
goto block_119;
}
}
else
{
uint8_t x_129; 
x_129 = lean_unbox(x_121);
lean_dec(x_121);
x_90 = x_129;
x_91 = x_123;
goto block_119;
}
}
else
{
lean_object* x_130; 
lean_dec(x_121);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_130 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13);
x_133 = l_Lean_mkApp3(x_132, x_2, x_3, x_131);
x_134 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_133, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_142; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_130, 0);
x_142 = !lean_is_exclusive(x_130);
if (x_142 == 0)
{
x_136 = x_130;
x_137 = x_142;
goto block_141;
}
else
{
lean_inc(x_135);
lean_dec(x_130);
x_136 = lean_box(0);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_137 == 0)
{
x_138 = x_136;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_135);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_150; 
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_120, 0);
x_150 = !lean_is_exclusive(x_120);
if (x_150 == 0)
{
x_144 = x_120;
x_145 = x_150;
goto block_149;
}
else
{
lean_inc(x_143);
lean_dec(x_120);
x_144 = lean_box(0);
x_145 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_146; 
if (x_145 == 0)
{
x_146 = x_144;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_143);
x_146 = x_148;
goto block_147;
}
block_147:
{
return x_146;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_42 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
x_144 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_42, x_10);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
x_103 = x_2;
x_104 = x_3;
x_105 = x_4;
x_106 = x_5;
x_107 = x_6;
x_108 = x_7;
x_109 = x_8;
x_110 = x_9;
x_111 = x_10;
x_112 = x_11;
goto block_143;
}
else
{
lean_object* x_147; 
x_147 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec_ref(x_147);
lean_inc_ref(x_1);
x_148 = l_Lean_MessageData_ofExpr(x_1);
x_149 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_42, x_148, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_149) == 0)
{
lean_dec_ref(x_149);
x_103 = x_2;
x_104 = x_3;
x_105 = x_4;
x_106 = x_5;
x_107 = x_6;
x_108 = x_7;
x_109 = x_8;
x_110 = x_9;
x_111 = x_10;
x_112 = x_11;
goto block_143;
}
else
{
lean_dec_ref(x_1);
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
return x_149;
}
}
else
{
lean_dec_ref(x_1);
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
return x_147;
}
}
block_41:
{
lean_object* x_28; 
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
x_28 = l_Lean_Meta_Simp_Result_getProof(x_21, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__2, &l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
lean_inc_ref(x_17);
lean_inc_ref(x_14);
x_31 = l_Lean_mkApp5(x_30, x_14, x_20, x_17, x_18, x_29);
x_32 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_17, x_31, x_19, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_23);
lean_dec(x_22);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_28, 0);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
x_34 = x_28;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
block_102:
{
lean_object* x_54; 
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc_ref(x_14);
x_54 = l_Lean_Meta_Grind_mkEqTrueProof(x_14, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
lean_inc(x_55);
lean_inc_ref(x_14);
x_56 = l_Lean_Meta_mkOfEqTrueCore(x_14, x_55);
x_57 = lean_expr_instantiate1(x_15, x_56);
lean_dec_ref(x_56);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_58 = lean_grind_preprocess(x_57, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_44);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_62);
x_63 = lean_box(0);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc_ref(x_62);
x_64 = lean_grind_internalize(x_62, x_61, x_63, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec_ref(x_64);
x_65 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_42, x_52);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
x_67 = l_Lean_mkLambda(x_13, x_16, x_14, x_15);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
if (x_68 == 0)
{
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_45);
x_17 = x_62;
x_18 = x_55;
x_19 = x_43;
x_20 = x_67;
x_21 = x_59;
x_22 = x_44;
x_23 = x_46;
x_24 = x_50;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
goto block_41;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_Meta_Grind_updateLastTag(x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_45);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_69);
x_70 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__8, &l_Lean_Meta_Grind_propagateForallPropUp___closed__8_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__8);
lean_inc_ref(x_62);
x_71 = l_Lean_MessageData_ofExpr(x_62);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__10, &l_Lean_Meta_Grind_propagateForallPropUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__10);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc_ref(x_1);
x_75 = l_Lean_indentExpr(x_1);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_42, x_76, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_17 = x_62;
x_18 = x_55;
x_19 = x_43;
x_20 = x_67;
x_21 = x_59;
x_22 = x_44;
x_23 = x_46;
x_24 = x_50;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
goto block_41;
}
else
{
lean_dec_ref(x_67);
lean_dec_ref(x_62);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_46);
lean_dec(x_44);
lean_dec_ref(x_1);
return x_77;
}
}
else
{
lean_dec_ref(x_67);
lean_dec_ref(x_62);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_46);
lean_dec(x_44);
lean_dec_ref(x_1);
return x_69;
}
}
}
else
{
lean_dec_ref(x_62);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_1);
return x_64;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_1);
x_78 = lean_ctor_get(x_60, 0);
x_85 = !lean_is_exclusive(x_60);
if (x_85 == 0)
{
x_79 = x_60;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_60);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_1);
x_86 = lean_ctor_get(x_58, 0);
x_93 = !lean_is_exclusive(x_58);
if (x_93 == 0)
{
x_87 = x_58;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_58);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_54, 0);
x_101 = !lean_is_exclusive(x_54);
if (x_101 == 0)
{
x_95 = x_54;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_54);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
block_143:
{
uint8_t x_113; 
x_113 = l_Lean_Expr_hasLooseBVars(x_15);
if (x_113 == 0)
{
lean_object* x_114; 
lean_inc_ref(x_15);
lean_inc_ref(x_14);
x_114 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_14, x_15, x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
return x_114;
}
else
{
lean_object* x_115; 
lean_inc_ref(x_14);
x_115 = l_Lean_Meta_Grind_isEqTrue___redArg(x_14, x_103, x_107, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_134; 
x_116 = lean_ctor_get(x_115, 0);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
x_117 = x_115;
x_118 = x_134;
goto block_133;
}
else
{
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_box(0);
x_118 = x_134;
goto block_133;
}
block_133:
{
uint8_t x_119; 
x_119 = lean_unbox(x_116);
lean_dec(x_116);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_1);
x_120 = lean_box(0);
if (x_118 == 0)
{
lean_ctor_set(x_117, 0, x_120);
x_121 = x_117;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; 
lean_del_object(x_117);
x_124 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_42, x_111);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = 0;
x_127 = lean_unbox(x_125);
lean_dec(x_125);
if (x_127 == 0)
{
x_43 = x_126;
x_44 = x_103;
x_45 = x_104;
x_46 = x_105;
x_47 = x_106;
x_48 = x_107;
x_49 = x_108;
x_50 = x_109;
x_51 = x_110;
x_52 = x_111;
x_53 = x_112;
goto block_102;
}
else
{
lean_object* x_128; 
x_128 = l_Lean_Meta_Grind_updateLastTag(x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_128);
x_129 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__12, &l_Lean_Meta_Grind_propagateForallPropUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12);
lean_inc_ref(x_1);
x_130 = l_Lean_MessageData_ofExpr(x_1);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_42, x_131, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_43 = x_126;
x_44 = x_103;
x_45 = x_104;
x_46 = x_105;
x_47 = x_106;
x_48 = x_107;
x_49 = x_108;
x_50 = x_109;
x_51 = x_110;
x_52 = x_111;
x_53 = x_112;
goto block_102;
}
else
{
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_1);
return x_132;
}
}
else
{
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_1);
return x_128;
}
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_142; 
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_115, 0);
x_142 = !lean_is_exclusive(x_115);
if (x_142 == 0)
{
x_136 = x_115;
x_137 = x_142;
goto block_141;
}
else
{
lean_inc(x_135);
lean_dec(x_115);
x_136 = lean_box(0);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_137 == 0)
{
x_138 = x_136;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_135);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
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
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateForallPropUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1));
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_5);
x_15 = lean_box(0);
return x_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
x_11 = 0;
x_12 = 1;
x_13 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_1, x_10, x_2, x_3, x_4, x_11, x_11, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_26 = l_Lean_Exception_isInterrupt(x_14);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_14);
x_15 = x_27;
goto block_25;
}
else
{
lean_dec(x_14);
x_15 = x_26;
goto block_25;
}
block_25:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_13, 0);
lean_dec(x_24);
x_16 = x_13;
x_17 = x_23;
goto block_22;
}
else
{
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_expr_eqv(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_array_uget_borrowed(x_2, x_3);
x_8 = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(x_6, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(x_2, x_1, x_7, x_8);
if (x_9 == 0)
{
return x_5;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_Meta_Grind_AnchorRef_matches(x_6, x_1);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_getAnchorRefs___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_66; 
x_13 = lean_ctor_get(x_12, 0);
x_66 = !lean_is_exclusive(x_12);
if (x_66 == 0)
{
x_14 = x_12;
x_15 = x_66;
goto block_65;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_66;
goto block_65;
}
block_65:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_del_object(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_17 = lean_infer_type(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_getAnchor(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_43; 
x_20 = lean_ctor_get(x_19, 0);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
x_21 = x_19;
x_22 = x_43;
goto block_42;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_16);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_16);
x_26 = lean_box(x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_26);
x_27 = x_21;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
else
{
if (x_25 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
lean_dec(x_16);
x_30 = lean_box(x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_30);
x_31 = x_21;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
size_t x_34; size_t x_35; uint64_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_24);
x_36 = lean_unbox_uint64(x_20);
lean_dec(x_20);
x_37 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_36, x_16, x_34, x_35);
lean_dec(x_16);
x_38 = lean_box(x_37);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_38);
x_39 = x_21;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_16);
x_44 = lean_ctor_get(x_19, 0);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
x_45 = x_19;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_19);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
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
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_52 = lean_ctor_get(x_17, 0);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
x_53 = x_17;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_17);
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
else
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_60 = 1;
x_61 = lean_box(x_60);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_61);
x_62 = x_14;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_12, 0);
x_74 = !lean_is_exclusive(x_12);
if (x_74 == 0)
{
x_68 = x_12;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_12);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_4, x_3);
if (x_22 == 0)
{
lean_object* x_23; 
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
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_uget_borrowed(x_2, x_4);
x_25 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_5, x_24);
if (x_25 == 0)
{
x_17 = x_5;
goto block_21;
}
else
{
lean_object* x_26; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_24);
x_26 = l_Lean_Meta_Grind_activateTheorem(x_24, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_26);
x_27 = lean_ctor_get(x_24, 3);
lean_inc(x_27);
x_28 = lean_array_push(x_5, x_27);
x_17 = x_28;
goto block_21;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
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
lean_dec_ref(x_5);
lean_dec(x_1);
x_29 = lean_ctor_get(x_26, 0);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
x_30 = x_26;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_26);
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
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_2);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_131; 
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
x_131 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_232; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
lean_inc(x_132);
x_232 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(x_132);
if (lean_obj_tag(x_232) == 1)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; uint8_t x_240; 
x_233 = lean_ctor_get(x_232, 0);
x_240 = !lean_is_exclusive(x_232);
if (x_240 == 0)
{
x_234 = x_232;
x_235 = x_240;
goto block_239;
}
else
{
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_box(0);
x_235 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_236; 
if (x_235 == 0)
{
x_236 = x_234;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_233);
x_236 = x_238;
goto block_237;
}
block_237:
{
x_133 = x_236;
x_134 = x_2;
x_135 = x_3;
x_136 = x_4;
x_137 = x_5;
x_138 = x_6;
x_139 = x_7;
x_140 = x_8;
x_141 = x_9;
x_142 = x_10;
x_143 = x_11;
goto block_231;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_301; 
lean_dec(x_232);
x_241 = lean_st_ref_take(x_2);
x_242 = lean_ctor_get(x_241, 0);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_242, 13);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_241, 1);
x_301 = !lean_is_exclusive(x_241);
if (x_301 == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_241, 0);
lean_dec(x_302);
x_245 = x_241;
x_246 = x_301;
goto block_300;
}
else
{
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_box(0);
x_246 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_298; 
x_247 = lean_ctor_get(x_242, 0);
x_248 = lean_ctor_get(x_242, 1);
x_249 = lean_ctor_get(x_242, 2);
x_250 = lean_ctor_get(x_242, 3);
x_251 = lean_ctor_get(x_242, 4);
x_252 = lean_ctor_get(x_242, 5);
x_253 = lean_ctor_get(x_242, 6);
x_254 = lean_ctor_get(x_242, 7);
x_255 = lean_ctor_get(x_242, 8);
x_256 = lean_ctor_get_uint8(x_242, sizeof(void*)*18);
x_257 = lean_ctor_get(x_242, 9);
x_258 = lean_ctor_get(x_242, 10);
x_259 = lean_ctor_get(x_242, 11);
x_260 = lean_ctor_get(x_242, 12);
x_261 = lean_ctor_get(x_242, 14);
x_262 = lean_ctor_get(x_242, 15);
x_263 = lean_ctor_get(x_242, 16);
x_264 = lean_ctor_get(x_242, 17);
x_298 = !lean_is_exclusive(x_242);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_242, 13);
lean_dec(x_299);
x_265 = x_242;
x_266 = x_298;
goto block_297;
}
else
{
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_242);
x_265 = lean_box(0);
x_266 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_296; 
x_267 = lean_ctor_get(x_243, 0);
x_268 = lean_ctor_get(x_243, 1);
x_269 = lean_ctor_get(x_243, 2);
x_270 = lean_ctor_get(x_243, 3);
x_271 = lean_ctor_get(x_243, 4);
x_272 = lean_ctor_get(x_243, 5);
x_273 = lean_ctor_get(x_243, 6);
x_274 = lean_ctor_get(x_243, 7);
x_275 = lean_ctor_get(x_243, 8);
x_276 = lean_ctor_get(x_243, 9);
x_277 = lean_ctor_get(x_243, 10);
x_296 = !lean_is_exclusive(x_243);
if (x_296 == 0)
{
x_278 = x_243;
x_279 = x_296;
goto block_295;
}
else
{
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_243);
x_278 = lean_box(0);
x_279 = x_296;
goto block_295;
}
block_295:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_unsigned_to_nat(1u);
x_281 = lean_nat_add(x_275, x_280);
if (x_279 == 0)
{
lean_ctor_set(x_278, 8, x_281);
x_282 = x_278;
goto block_293;
}
else
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_294, 0, x_267);
lean_ctor_set(x_294, 1, x_268);
lean_ctor_set(x_294, 2, x_269);
lean_ctor_set(x_294, 3, x_270);
lean_ctor_set(x_294, 4, x_271);
lean_ctor_set(x_294, 5, x_272);
lean_ctor_set(x_294, 6, x_273);
lean_ctor_set(x_294, 7, x_274);
lean_ctor_set(x_294, 8, x_281);
lean_ctor_set(x_294, 9, x_276);
lean_ctor_set(x_294, 10, x_277);
x_282 = x_294;
goto block_293;
}
block_293:
{
lean_object* x_283; 
if (x_266 == 0)
{
lean_ctor_set(x_265, 13, x_282);
x_283 = x_265;
goto block_291;
}
else
{
lean_object* x_292; 
x_292 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_292, 0, x_247);
lean_ctor_set(x_292, 1, x_248);
lean_ctor_set(x_292, 2, x_249);
lean_ctor_set(x_292, 3, x_250);
lean_ctor_set(x_292, 4, x_251);
lean_ctor_set(x_292, 5, x_252);
lean_ctor_set(x_292, 6, x_253);
lean_ctor_set(x_292, 7, x_254);
lean_ctor_set(x_292, 8, x_255);
lean_ctor_set(x_292, 9, x_257);
lean_ctor_set(x_292, 10, x_258);
lean_ctor_set(x_292, 11, x_259);
lean_ctor_set(x_292, 12, x_260);
lean_ctor_set(x_292, 13, x_282);
lean_ctor_set(x_292, 14, x_261);
lean_ctor_set(x_292, 15, x_262);
lean_ctor_set(x_292, 16, x_263);
lean_ctor_set(x_292, 17, x_264);
lean_ctor_set_uint8(x_292, sizeof(void*)*18, x_256);
x_283 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_284; 
if (x_246 == 0)
{
lean_ctor_set(x_245, 0, x_283);
x_284 = x_245;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_283);
lean_ctor_set(x_290, 1, x_244);
x_284 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_st_ref_set(x_2, x_284);
x_286 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3));
x_287 = lean_name_append_index_after(x_286, x_275);
x_288 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_133 = x_288;
x_134 = x_2;
x_135 = x_3;
x_136 = x_4;
x_137 = x_5;
x_138 = x_6;
x_139 = x_7;
x_140 = x_8;
x_141 = x_9;
x_142 = x_10;
x_143 = x_11;
goto block_231;
}
}
}
}
}
}
}
block_231:
{
lean_object* x_144; lean_object* x_145; 
lean_inc_ref(x_1);
x_144 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_132);
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc_ref(x_144);
x_145 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_144, x_135, x_136, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_222; 
x_146 = lean_ctor_get(x_145, 0);
x_222 = !lean_is_exclusive(x_145);
if (x_222 == 0)
{
x_147 = x_145;
x_148 = x_222;
goto block_221;
}
else
{
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_box(0);
x_148 = x_222;
goto block_221;
}
block_221:
{
uint8_t x_149; 
x_149 = lean_unbox(x_146);
lean_dec(x_146);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_150 = lean_box(0);
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_150);
x_151 = x_147;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_del_object(x_147);
x_154 = lean_st_ref_get(x_134);
x_155 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_134);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = l_Lean_Meta_Grind_getSymbolPriorities___redArg(x_136);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_unsigned_to_nat(1000u);
x_160 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
x_161 = 0;
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_158);
lean_inc_ref(x_144);
lean_inc_ref(x_133);
x_162 = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(x_133, x_160, x_144, x_159, x_158, x_161, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_array_size(x_163);
x_165 = 0;
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_137);
lean_inc_ref(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_156);
x_166 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_156, x_163, x_164, x_165, x_160, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
lean_dec(x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = lean_box(6);
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_158);
lean_inc_ref(x_144);
lean_inc_ref(x_133);
x_169 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_133, x_144, x_168, x_158, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_170);
lean_dec(x_154);
x_171 = lean_ctor_get(x_170, 13);
lean_inc_ref(x_171);
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 3);
lean_inc_ref(x_172);
lean_dec_ref(x_171);
x_173 = lean_ctor_get(x_169, 0);
lean_inc(x_173);
lean_dec_ref(x_169);
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_172, 2);
lean_inc(x_174);
lean_dec_ref(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
lean_dec_ref(x_173);
x_176 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_167, x_175);
if (x_176 == 0)
{
lean_dec(x_175);
x_99 = x_158;
x_100 = x_156;
x_101 = x_133;
x_102 = x_161;
x_103 = x_174;
x_104 = x_144;
x_105 = x_167;
x_106 = x_134;
x_107 = x_135;
x_108 = x_136;
x_109 = x_137;
x_110 = x_138;
x_111 = x_139;
x_112 = x_140;
x_113 = x_141;
x_114 = x_142;
x_115 = x_143;
goto block_130;
}
else
{
lean_object* x_177; 
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_137);
lean_inc_ref(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_156);
lean_inc(x_175);
x_177 = l_Lean_Meta_Grind_activateTheorem(x_175, x_156, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec_ref(x_177);
x_178 = lean_ctor_get(x_175, 3);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_array_push(x_167, x_178);
x_99 = x_158;
x_100 = x_156;
x_101 = x_133;
x_102 = x_161;
x_103 = x_174;
x_104 = x_144;
x_105 = x_179;
x_106 = x_134;
x_107 = x_135;
x_108 = x_136;
x_109 = x_137;
x_110 = x_138;
x_111 = x_139;
x_112 = x_140;
x_113 = x_141;
x_114 = x_142;
x_115 = x_143;
goto block_130;
}
else
{
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
return x_177;
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_173);
x_180 = lean_ctor_get(x_172, 2);
lean_inc(x_180);
lean_dec_ref(x_172);
x_99 = x_158;
x_100 = x_156;
x_101 = x_133;
x_102 = x_161;
x_103 = x_180;
x_104 = x_144;
x_105 = x_167;
x_106 = x_134;
x_107 = x_135;
x_108 = x_136;
x_109 = x_137;
x_110 = x_138;
x_111 = x_139;
x_112 = x_140;
x_113 = x_141;
x_114 = x_142;
x_115 = x_143;
goto block_130;
}
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_188; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_181 = lean_ctor_get(x_169, 0);
x_188 = !lean_is_exclusive(x_169);
if (x_188 == 0)
{
x_182 = x_169;
x_183 = x_188;
goto block_187;
}
else
{
lean_inc(x_181);
lean_dec(x_169);
x_182 = lean_box(0);
x_183 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_184; 
if (x_183 == 0)
{
x_184 = x_182;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_181);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_196; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_166, 0);
x_196 = !lean_is_exclusive(x_166);
if (x_196 == 0)
{
x_190 = x_166;
x_191 = x_196;
goto block_195;
}
else
{
lean_inc(x_189);
lean_dec(x_166);
x_190 = lean_box(0);
x_191 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_192; 
if (x_191 == 0)
{
x_192 = x_190;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_189);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_162, 0);
x_204 = !lean_is_exclusive(x_162);
if (x_204 == 0)
{
x_198 = x_162;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_162);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_212; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_157, 0);
x_212 = !lean_is_exclusive(x_157);
if (x_212 == 0)
{
x_206 = x_157;
x_207 = x_212;
goto block_211;
}
else
{
lean_inc(x_205);
lean_dec(x_157);
x_206 = lean_box(0);
x_207 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_208; 
if (x_207 == 0)
{
x_208 = x_206;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_205);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_220; 
lean_dec(x_154);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_213 = lean_ctor_get(x_155, 0);
x_220 = !lean_is_exclusive(x_155);
if (x_220 == 0)
{
x_214 = x_155;
x_215 = x_220;
goto block_219;
}
else
{
lean_inc(x_213);
lean_dec(x_155);
x_214 = lean_box(0);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_215 == 0)
{
x_216 = x_214;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_213);
x_216 = x_218;
goto block_217;
}
block_217:
{
return x_216;
}
}
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_230; 
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
x_223 = lean_ctor_get(x_145, 0);
x_230 = !lean_is_exclusive(x_145);
if (x_230 == 0)
{
x_224 = x_145;
x_225 = x_230;
goto block_229;
}
else
{
lean_inc(x_223);
lean_dec(x_145);
x_224 = lean_box(0);
x_225 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_226; 
if (x_225 == 0)
{
x_226 = x_224;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_223);
x_226 = x_228;
goto block_227;
}
block_227:
{
return x_226;
}
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_310; 
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
x_303 = lean_ctor_get(x_131, 0);
x_310 = !lean_is_exclusive(x_131);
if (x_310 == 0)
{
x_304 = x_131;
x_305 = x_310;
goto block_309;
}
else
{
lean_inc(x_303);
lean_dec(x_131);
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
block_62:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_60; 
x_24 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_25 = lean_ctor_get(x_24, 0);
x_60 = !lean_is_exclusive(x_24);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_24, 1);
lean_dec(x_61);
x_26 = x_24;
x_27 = x_60;
goto block_59;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_28);
lean_dec_ref(x_25);
x_29 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_nat_dec_eq(x_30, x_13);
lean_dec(x_13);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_del_object(x_26);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Grind_getConfig___redArg(x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_50; 
x_35 = lean_ctor_get(x_34, 0);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
x_36 = x_34;
x_37 = x_50;
goto block_49;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_50;
goto block_49;
}
block_49:
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_35, sizeof(void*)*11 + 14);
lean_dec(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_del_object(x_26);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_39 = lean_box(0);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_39);
x_40 = x_36;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_del_object(x_36);
x_43 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
x_44 = l_Lean_indentExpr(x_1);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_44);
lean_ctor_set(x_26, 0, x_43);
x_45 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
x_45 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_46; 
x_46 = l_Lean_Meta_Grind_reportIssue(x_45, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_del_object(x_26);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_34, 0);
x_58 = !lean_is_exclusive(x_34);
if (x_58 == 0)
{
x_52 = x_34;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
block_98:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_st_ref_get(x_69);
x_80 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_80, 13);
lean_inc_ref(x_81);
lean_dec_ref(x_80);
x_82 = lean_ctor_get(x_81, 3);
lean_inc_ref(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 2);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_nat_dec_eq(x_83, x_67);
lean_dec(x_83);
if (x_84 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
x_13 = x_67;
x_14 = x_69;
x_15 = x_70;
x_16 = x_71;
x_17 = x_72;
x_18 = x_73;
x_19 = x_74;
x_20 = x_75;
x_21 = x_76;
x_22 = x_77;
x_23 = x_78;
goto block_62;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(x_85, 0, x_66);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
x_86 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_65, x_68, x_85, x_63, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
if (lean_obj_tag(x_87) == 1)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc(x_69);
x_89 = l_Lean_Meta_Grind_activateTheorem(x_88, x_64, x_69, x_70, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
x_13 = x_67;
x_14 = x_69;
x_15 = x_70;
x_16 = x_71;
x_17 = x_72;
x_18 = x_73;
x_19 = x_74;
x_20 = x_75;
x_21 = x_76;
x_22 = x_77;
x_23 = x_78;
goto block_62;
}
else
{
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec_ref(x_1);
return x_89;
}
}
else
{
lean_dec(x_87);
lean_dec(x_64);
x_13 = x_67;
x_14 = x_69;
x_15 = x_70;
x_16 = x_71;
x_17 = x_72;
x_18 = x_73;
x_19 = x_74;
x_20 = x_75;
x_21 = x_76;
x_22 = x_77;
x_23 = x_78;
goto block_62;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_64);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_86, 0);
x_97 = !lean_is_exclusive(x_86);
if (x_97 == 0)
{
x_91 = x_86;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
block_130:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_box(7);
lean_inc(x_115);
lean_inc_ref(x_114);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc_ref(x_99);
lean_inc_ref(x_104);
lean_inc_ref(x_101);
x_117 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_101, x_104, x_116, x_99, x_112, x_113, x_114, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
if (lean_obj_tag(x_118) == 1)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_105, x_119);
lean_dec_ref(x_105);
if (x_120 == 0)
{
lean_dec(x_119);
x_63 = x_99;
x_64 = x_100;
x_65 = x_101;
x_66 = x_102;
x_67 = x_103;
x_68 = x_104;
x_69 = x_106;
x_70 = x_107;
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
x_74 = x_111;
x_75 = x_112;
x_76 = x_113;
x_77 = x_114;
x_78 = x_115;
goto block_98;
}
else
{
lean_object* x_121; 
lean_inc(x_115);
lean_inc_ref(x_114);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc(x_111);
lean_inc_ref(x_110);
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_100);
x_121 = l_Lean_Meta_Grind_activateTheorem(x_119, x_100, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_115);
if (lean_obj_tag(x_121) == 0)
{
lean_dec_ref(x_121);
x_63 = x_99;
x_64 = x_100;
x_65 = x_101;
x_66 = x_102;
x_67 = x_103;
x_68 = x_104;
x_69 = x_106;
x_70 = x_107;
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
x_74 = x_111;
x_75 = x_112;
x_76 = x_113;
x_77 = x_114;
x_78 = x_115;
goto block_98;
}
else
{
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_1);
return x_121;
}
}
}
else
{
lean_dec(x_118);
lean_dec_ref(x_105);
x_63 = x_99;
x_64 = x_100;
x_65 = x_101;
x_66 = x_102;
x_67 = x_103;
x_68 = x_104;
x_69 = x_106;
x_70 = x_107;
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
x_74 = x_111;
x_75 = x_112;
x_76 = x_113;
x_77 = x_114;
x_78 = x_115;
goto block_98;
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_129; 
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_1);
x_122 = lean_ctor_get(x_117, 0);
x_129 = !lean_is_exclusive(x_117);
if (x_129 == 0)
{
x_123 = x_117;
x_124 = x_129;
goto block_128;
}
else
{
lean_inc(x_122);
lean_dec(x_117);
x_123 = lean_box(0);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_124 == 0)
{
x_125 = x_123;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_122);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_125; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc_ref(x_1);
x_125 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_inc_ref(x_1);
x_128 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_209; 
x_129 = lean_ctor_get(x_128, 0);
x_209 = !lean_is_exclusive(x_128);
if (x_209 == 0)
{
x_130 = x_128;
x_131 = x_209;
goto block_208;
}
else
{
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = x_209;
goto block_208;
}
block_208:
{
uint8_t x_132; 
x_132 = lean_unbox(x_129);
lean_dec(x_129);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_1);
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
x_133 = lean_box(0);
if (x_131 == 0)
{
lean_ctor_set(x_130, 0, x_133);
x_134 = x_130;
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
else
{
lean_object* x_137; 
lean_del_object(x_130);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_137 = l_Lean_Meta_Grind_eqResolution(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_199; 
x_139 = lean_ctor_get(x_138, 0);
x_199 = !lean_is_exclusive(x_138);
if (x_199 == 0)
{
x_140 = x_138;
x_141 = x_199;
goto block_198;
}
else
{
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_box(0);
x_141 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_197; 
x_142 = lean_ctor_get(x_139, 0);
x_143 = lean_ctor_get(x_139, 1);
x_197 = !lean_is_exclusive(x_139);
if (x_197 == 0)
{
x_144 = x_139;
x_145 = x_197;
goto block_196;
}
else
{
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_139);
x_144 = lean_box(0);
x_145 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
x_184 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_183, x_10);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_unbox(x_185);
lean_dec(x_185);
if (x_186 == 0)
{
lean_del_object(x_144);
x_146 = x_2;
x_147 = x_3;
x_148 = x_4;
x_149 = x_5;
x_150 = x_6;
x_151 = x_7;
x_152 = x_8;
x_153 = x_9;
x_154 = x_10;
x_155 = x_11;
goto block_182;
}
else
{
lean_object* x_187; 
x_187 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec_ref(x_187);
lean_inc_ref(x_1);
x_188 = l_Lean_MessageData_ofExpr(x_1);
x_189 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__3, &l_Lean_Meta_Grind_propagateForallPropDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__3);
if (x_145 == 0)
{
lean_ctor_set_tag(x_144, 7);
lean_ctor_set(x_144, 1, x_189);
lean_ctor_set(x_144, 0, x_188);
x_190 = x_144;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_189);
x_190 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_inc(x_142);
x_191 = l_Lean_MessageData_ofExpr(x_142);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_183, x_192, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_193) == 0)
{
lean_dec_ref(x_193);
x_146 = x_2;
x_147 = x_3;
x_148 = x_4;
x_149 = x_5;
x_150 = x_6;
x_151 = x_7;
x_152 = x_8;
x_153 = x_9;
x_154 = x_10;
x_155 = x_11;
goto block_182;
}
else
{
lean_dec(x_143);
lean_dec(x_142);
lean_del_object(x_140);
lean_dec_ref(x_1);
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
return x_193;
}
}
}
else
{
lean_del_object(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_del_object(x_140);
lean_dec_ref(x_1);
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
return x_187;
}
}
block_182:
{
lean_object* x_156; 
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_152);
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc_ref(x_1);
x_156 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_146, x_147, x_148, x_149, x_150, x_151, x_152, x_153, x_154, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec_ref(x_156);
x_158 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_146);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
lean_inc_ref(x_1);
x_160 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_157);
x_161 = l_Lean_Expr_app___override(x_143, x_160);
lean_inc_ref(x_1);
if (x_141 == 0)
{
lean_ctor_set_tag(x_140, 4);
lean_ctor_set(x_140, 0, x_1);
x_162 = x_140;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_165, 0, x_1);
x_162 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_163; 
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_152);
x_163 = l_Lean_Meta_Grind_addNewRawFact(x_161, x_142, x_159, x_162, x_146, x_147, x_148, x_149, x_150, x_151, x_152, x_153, x_154, x_155);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
x_70 = x_146;
x_71 = x_147;
x_72 = x_148;
x_73 = x_149;
x_74 = x_150;
x_75 = x_151;
x_76 = x_152;
x_77 = x_153;
x_78 = x_154;
x_79 = x_155;
goto block_124;
}
else
{
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec_ref(x_1);
return x_163;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_173; 
lean_dec(x_157);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_143);
lean_dec(x_142);
lean_del_object(x_140);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_158, 0);
x_173 = !lean_is_exclusive(x_158);
if (x_173 == 0)
{
x_167 = x_158;
x_168 = x_173;
goto block_172;
}
else
{
lean_inc(x_166);
lean_dec(x_158);
x_167 = lean_box(0);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_168 == 0)
{
x_169 = x_167;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_166);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_181; 
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_143);
lean_dec(x_142);
lean_del_object(x_140);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_156, 0);
x_181 = !lean_is_exclusive(x_156);
if (x_181 == 0)
{
x_175 = x_156;
x_176 = x_181;
goto block_180;
}
else
{
lean_inc(x_174);
lean_dec(x_156);
x_175 = lean_box(0);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_176 == 0)
{
x_177 = x_175;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
}
}
}
else
{
lean_dec(x_138);
x_70 = x_2;
x_71 = x_3;
x_72 = x_4;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_10;
x_79 = x_11;
goto block_124;
}
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec_ref(x_1);
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
x_200 = lean_ctor_get(x_137, 0);
x_207 = !lean_is_exclusive(x_137);
if (x_207 == 0)
{
x_201 = x_137;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_137);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_217; 
lean_dec_ref(x_1);
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
x_210 = lean_ctor_get(x_128, 0);
x_217 = !lean_is_exclusive(x_128);
if (x_217 == 0)
{
x_211 = x_128;
x_212 = x_217;
goto block_216;
}
else
{
lean_inc(x_210);
lean_dec(x_128);
x_211 = lean_box(0);
x_212 = x_217;
goto block_216;
}
block_216:
{
lean_object* x_213; 
if (x_212 == 0)
{
x_213 = x_211;
goto block_214;
}
else
{
lean_object* x_215; 
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_210);
x_213 = x_215;
goto block_214;
}
block_214:
{
return x_213;
}
}
}
}
else
{
lean_object* x_218; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_14);
x_218 = l_Lean_Meta_isProp(x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; uint8_t x_264; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_264 = l_Lean_Expr_hasLooseBVars(x_15);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = lean_unbox(x_219);
lean_dec(x_219);
if (x_265 == 0)
{
goto block_263;
}
else
{
if (x_264 == 0)
{
lean_object* x_266; 
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_266 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__10, &l_Lean_Meta_Grind_propagateForallPropDown___closed__10_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__10);
lean_inc(x_267);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
x_269 = l_Lean_mkApp3(x_268, x_14, x_15, x_267);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_14);
x_270 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_14, x_269, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec_ref(x_270);
x_271 = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__13, &l_Lean_Meta_Grind_propagateForallPropDown___closed__13_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__13);
lean_inc_ref(x_15);
x_272 = l_Lean_mkApp3(x_271, x_14, x_15, x_267);
x_273 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_15, x_272, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_273;
}
else
{
lean_dec(x_267);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_270;
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_274 = lean_ctor_get(x_266, 0);
x_281 = !lean_is_exclusive(x_266);
if (x_281 == 0)
{
x_275 = x_266;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_266);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
goto block_263;
}
}
}
else
{
lean_dec(x_219);
goto block_263;
}
block_263:
{
lean_object* x_220; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_14);
x_220 = l_Lean_Meta_getLevel(x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
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
x_222 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
lean_inc_ref(x_15);
x_224 = l_Lean_mkNot(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
x_225 = l_Lean_mkLambda(x_13, x_16, x_14, x_224);
x_226 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__5));
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_229);
lean_inc_ref(x_230);
x_231 = l_Lean_mkConst(x_228, x_230);
lean_inc_ref(x_14);
x_232 = l_Lean_mkAppB(x_231, x_14, x_225);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
x_233 = l_Lean_mkLambda(x_13, x_16, x_14, x_15);
x_234 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__7));
x_235 = l_Lean_mkConst(x_234, x_230);
lean_inc_ref(x_14);
x_236 = l_Lean_mkApp3(x_235, x_14, x_233, x_223);
x_237 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_237, 0, x_1);
x_238 = l_Lean_Meta_Grind_addNewRawFact(x_236, x_232, x_227, x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_246; 
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_221);
lean_dec_ref(x_1);
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
x_239 = lean_ctor_get(x_226, 0);
x_246 = !lean_is_exclusive(x_226);
if (x_246 == 0)
{
x_240 = x_226;
x_241 = x_246;
goto block_245;
}
else
{
lean_inc(x_239);
lean_dec(x_226);
x_240 = lean_box(0);
x_241 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_242; 
if (x_241 == 0)
{
x_242 = x_240;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_239);
x_242 = x_244;
goto block_243;
}
block_243:
{
return x_242;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; uint8_t x_254; 
lean_dec(x_221);
lean_dec_ref(x_1);
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
x_247 = lean_ctor_get(x_222, 0);
x_254 = !lean_is_exclusive(x_222);
if (x_254 == 0)
{
x_248 = x_222;
x_249 = x_254;
goto block_253;
}
else
{
lean_inc(x_247);
lean_dec(x_222);
x_248 = lean_box(0);
x_249 = x_254;
goto block_253;
}
block_253:
{
lean_object* x_250; 
if (x_249 == 0)
{
x_250 = x_248;
goto block_251;
}
else
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_247);
x_250 = x_252;
goto block_251;
}
block_251:
{
return x_250;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_262; 
lean_dec_ref(x_1);
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
x_255 = lean_ctor_get(x_220, 0);
x_262 = !lean_is_exclusive(x_220);
if (x_262 == 0)
{
x_256 = x_220;
x_257 = x_262;
goto block_261;
}
else
{
lean_inc(x_255);
lean_dec(x_220);
x_256 = lean_box(0);
x_257 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_258; 
if (x_257 == 0)
{
x_258 = x_256;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_255);
x_258 = x_260;
goto block_259;
}
block_259:
{
return x_258;
}
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_289; 
lean_dec_ref(x_1);
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
x_282 = lean_ctor_get(x_218, 0);
x_289 = !lean_is_exclusive(x_218);
if (x_289 == 0)
{
x_283 = x_218;
x_284 = x_289;
goto block_288;
}
else
{
lean_inc(x_282);
lean_dec(x_218);
x_283 = lean_box(0);
x_284 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_285; 
if (x_284 == 0)
{
x_285 = x_283;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_282);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_297; 
lean_dec_ref(x_1);
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
x_290 = lean_ctor_get(x_125, 0);
x_297 = !lean_is_exclusive(x_125);
if (x_297 == 0)
{
x_291 = x_125;
x_292 = x_297;
goto block_296;
}
else
{
lean_inc(x_290);
lean_dec(x_125);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_290);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
block_69:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_60; 
x_28 = lean_ctor_get(x_27, 0);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
x_29 = x_27;
x_30 = x_60;
goto block_59;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_60;
goto block_59;
}
block_59:
{
uint8_t x_31; 
x_31 = lean_unbox(x_28);
lean_dec(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_32 = lean_box(0);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_32);
x_33 = x_29;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; 
lean_del_object(x_29);
lean_inc(x_26);
lean_inc_ref(x_23);
lean_inc(x_25);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_21);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_22);
x_36 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_22, x_17, x_18, x_19, x_21, x_24, x_20, x_25, x_23, x_26);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_26);
lean_inc_ref(x_23);
lean_inc(x_25);
lean_inc_ref(x_20);
lean_inc_ref(x_21);
lean_inc_ref(x_18);
lean_inc(x_22);
lean_inc_ref(x_15);
x_38 = l_Lean_Meta_Grind_mkEqFalseProof(x_15, x_22, x_17, x_18, x_19, x_21, x_24, x_20, x_25, x_23, x_26);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(x_14);
x_41 = l_Lean_mkApp4(x_40, x_14, x_15, x_37, x_39);
x_42 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_14, x_41, x_22, x_18, x_21, x_20, x_25, x_23, x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_22);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_43 = lean_ctor_get(x_38, 0);
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
x_44 = x_38;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_51 = lean_ctor_get(x_36, 0);
x_58 = !lean_is_exclusive(x_36);
if (x_58 == 0)
{
x_52 = x_36;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_36);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_61 = lean_ctor_get(x_27, 0);
x_68 = !lean_is_exclusive(x_27);
if (x_68 == 0)
{
x_62 = x_27;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_27);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
block_124:
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasLooseBVars(x_15);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc_ref(x_15);
lean_inc_ref(x_14);
x_81 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_15, x_70);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_95; 
x_82 = lean_ctor_get(x_81, 0);
x_95 = !lean_is_exclusive(x_81);
if (x_95 == 0)
{
x_83 = x_81;
x_84 = x_95;
goto block_94;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_95;
goto block_94;
}
block_94:
{
uint8_t x_85; 
x_85 = lean_unbox(x_82);
lean_dec(x_82);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_86 = lean_box(0);
if (x_84 == 0)
{
lean_ctor_set(x_83, 0, x_86);
x_87 = x_83;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_86);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
else
{
lean_object* x_90; 
lean_del_object(x_83);
lean_inc_ref(x_15);
x_90 = l_Lean_Meta_Grind_isEqFalse___redArg(x_15, x_70, x_74, x_76, x_77, x_78, x_79);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
x_17 = x_71;
x_18 = x_72;
x_19 = x_73;
x_20 = x_76;
x_21 = x_74;
x_22 = x_70;
x_23 = x_78;
x_24 = x_75;
x_25 = x_77;
x_26 = x_79;
x_27 = x_90;
goto block_69;
}
else
{
lean_object* x_93; 
lean_dec_ref(x_90);
lean_inc(x_79);
lean_inc_ref(x_78);
lean_inc(x_77);
lean_inc_ref(x_76);
lean_inc_ref(x_14);
x_93 = l_Lean_Meta_isProp(x_14, x_76, x_77, x_78, x_79);
x_17 = x_71;
x_18 = x_72;
x_19 = x_73;
x_20 = x_76;
x_21 = x_74;
x_22 = x_70;
x_23 = x_78;
x_24 = x_75;
x_25 = x_77;
x_26 = x_79;
x_27 = x_93;
goto block_69;
}
}
else
{
x_17 = x_71;
x_18 = x_72;
x_19 = x_73;
x_20 = x_76;
x_21 = x_74;
x_22 = x_70;
x_23 = x_78;
x_24 = x_75;
x_25 = x_77;
x_26 = x_79;
x_27 = x_90;
goto block_69;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_96 = lean_ctor_get(x_81, 0);
x_103 = !lean_is_exclusive(x_81);
if (x_103 == 0)
{
x_97 = x_81;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
else
{
lean_object* x_104; 
lean_inc(x_79);
lean_inc_ref(x_78);
lean_inc(x_77);
lean_inc_ref(x_76);
lean_inc_ref(x_14);
x_104 = l_Lean_Meta_isProp(x_14, x_76, x_77, x_78, x_79);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_115; 
x_105 = lean_ctor_get(x_104, 0);
x_115 = !lean_is_exclusive(x_104);
if (x_115 == 0)
{
x_106 = x_104;
x_107 = x_115;
goto block_114;
}
else
{
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_box(0);
x_107 = x_115;
goto block_114;
}
block_114:
{
uint8_t x_108; 
x_108 = lean_unbox(x_105);
lean_dec(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
lean_del_object(x_106);
x_109 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_70, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_79);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_110 = lean_box(0);
if (x_107 == 0)
{
lean_ctor_set(x_106, 0, x_110);
x_111 = x_106;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_104, 0);
x_123 = !lean_is_exclusive(x_104);
if (x_123 == 0)
{
x_117 = x_104;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_104);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
}
else
{
lean_object* x_298; lean_object* x_299; 
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
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateForallPropDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_70; 
x_17 = lean_ctor_get(x_16, 0);
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
x_18 = x_16;
x_19 = x_70;
goto block_69;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_70;
goto block_69;
}
block_69:
{
uint8_t x_20; 
x_20 = lean_unbox(x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
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
x_21 = lean_box(0);
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
lean_object* x_25; uint8_t x_26; 
lean_del_object(x_18);
lean_inc_ref(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
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
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
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
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__5));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
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
goto block_15;
}
else
{
lean_object* x_34; 
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
x_34 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__2, &l_Lean_Meta_Grind_propagateExistsDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
x_39 = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__3, &l_Lean_Meta_Grind_propagateExistsDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
lean_inc_ref(x_27);
x_40 = l_Lean_Expr_app___override(x_27, x_39);
x_41 = l_Lean_Expr_headBeta(x_40);
x_42 = l_Lean_Expr_app___override(x_38, x_41);
x_43 = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__5));
x_44 = 0;
lean_inc_ref(x_30);
x_45 = l_Lean_mkForall(x_43, x_44, x_30, x_42);
x_46 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_47 = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__7));
x_48 = l_Lean_mkConst(x_47, x_46);
lean_inc_ref(x_1);
x_49 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_35);
x_50 = l_Lean_mkApp3(x_48, x_30, x_27, x_49);
x_51 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_51, 0, x_1);
x_52 = l_Lean_Meta_Grind_addNewRawFact(x_50, x_45, x_37, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
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
x_53 = lean_ctor_get(x_36, 0);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
x_54 = x_36;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
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
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
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
x_61 = lean_ctor_get(x_34, 0);
x_68 = !lean_is_exclusive(x_34);
if (x_68 == 0)
{
x_62 = x_34;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
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
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
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
x_71 = lean_ctor_get(x_16, 0);
x_78 = !lean_is_exclusive(x_16);
if (x_78 == 0)
{
x_72 = x_16;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_16);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateExistsDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__5));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1));
x_13 = l_Lean_Expr_appArg_x21(x_1);
x_14 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_2);
x_12 = l_Lean_Meta_getLevel(x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_simpForall___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = 0;
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__15));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__20));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__26));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__29));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__32));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__35));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__37, &l_Lean_Meta_Grind_simpForall___closed__37_once, _init_l_Lean_Meta_Grind_simpForall___closed__37);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__40));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_225; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_225 = l_Lean_Expr_hasLooseBVars(x_15);
if (x_225 == 0)
{
lean_object* x_226; 
lean_inc_ref(x_14);
x_226 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_14, x_6);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = 1;
x_254 = l_Lean_Expr_cleanupAnnotations(x_227);
x_255 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
x_256 = l_Lean_Expr_isConstOf(x_254, x_255);
if (x_256 == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
x_258 = l_Lean_Expr_isConstOf(x_254, x_257);
lean_dec_ref(x_254);
if (x_258 == 0)
{
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_263; uint8_t x_297; 
x_259 = lean_ctor_get(x_14, 0);
x_260 = lean_ctor_get(x_14, 1);
x_261 = lean_ctor_get(x_14, 2);
x_262 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 8);
x_297 = l_Lean_Expr_hasLooseBVars(x_261);
if (x_297 == 0)
{
x_263 = x_297;
goto block_296;
}
else
{
lean_object* x_298; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
x_298 = l_Lean_Meta_isProp(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
lean_dec_ref(x_298);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
x_263 = x_300;
goto block_296;
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_308; 
lean_dec_ref(x_14);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_301 = lean_ctor_get(x_298, 0);
x_308 = !lean_is_exclusive(x_298);
if (x_308 == 0)
{
x_302 = x_298;
x_303 = x_308;
goto block_307;
}
else
{
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_box(0);
x_303 = x_308;
goto block_307;
}
block_307:
{
lean_object* x_304; 
if (x_303 == 0)
{
x_304 = x_302;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_301);
x_304 = x_306;
goto block_305;
}
block_305:
{
return x_304;
}
}
}
}
block_296:
{
if (x_263 == 0)
{
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_inc_ref(x_261);
lean_inc_ref(x_260);
lean_inc(x_259);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_261);
lean_inc_ref(x_260);
lean_inc(x_259);
x_264 = l_Lean_mkLambda(x_259, x_262, x_260, x_261);
lean_inc_ref(x_260);
x_265 = l_Lean_Meta_getLevel(x_260, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_287; 
x_266 = lean_ctor_get(x_265, 0);
x_287 = !lean_is_exclusive(x_265);
if (x_287 == 0)
{
x_267 = x_265;
x_268 = x_287;
goto block_286;
}
else
{
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_box(0);
x_268 = x_287;
goto block_286;
}
block_286:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_269 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__5));
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_266);
lean_ctor_set(x_271, 1, x_270);
lean_inc_ref(x_271);
x_272 = l_Lean_mkConst(x_269, x_271);
x_273 = l_Lean_mkNot(x_261);
lean_inc_ref(x_260);
x_274 = l_Lean_mkLambda(x_259, x_262, x_260, x_273);
lean_inc_ref(x_260);
x_275 = l_Lean_mkAppB(x_272, x_260, x_274);
lean_inc_ref(x_15);
x_276 = l_Lean_mkOr(x_275, x_15);
x_277 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__18));
x_278 = l_Lean_mkConst(x_277, x_271);
x_279 = l_Lean_mkApp3(x_278, x_260, x_264, x_15);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set_uint8(x_281, sizeof(void*)*2, x_228);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
if (x_268 == 0)
{
lean_ctor_set(x_267, 0, x_282);
x_283 = x_267;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_282);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_295; 
lean_dec_ref(x_264);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_15);
x_288 = lean_ctor_get(x_265, 0);
x_295 = !lean_is_exclusive(x_265);
if (x_295 == 0)
{
x_289 = x_265;
x_290 = x_295;
goto block_294;
}
else
{
lean_inc(x_288);
lean_dec(x_265);
x_289 = lean_box(0);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_290 == 0)
{
x_291 = x_289;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_288);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
}
}
}
else
{
lean_object* x_309; 
lean_inc_ref(x_15);
x_309 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec_ref(x_309);
x_311 = l_Lean_Expr_cleanupAnnotations(x_310);
x_312 = l_Lean_Expr_isConstOf(x_311, x_255);
if (x_312 == 0)
{
uint8_t x_313; 
x_313 = l_Lean_Expr_isConstOf(x_311, x_257);
lean_dec_ref(x_311);
if (x_313 == 0)
{
lean_object* x_314; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
x_314 = l_Lean_Meta_isProp(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
x_229 = x_314;
goto block_253;
}
else
{
lean_object* x_317; 
lean_dec_ref(x_314);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
x_317 = l_Lean_Meta_isExprDefEq(x_14, x_15, x_5, x_6, x_7, x_8);
x_229 = x_317;
goto block_253;
}
}
else
{
x_229 = x_314;
goto block_253;
}
}
else
{
lean_object* x_318; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
x_318 = l_Lean_Meta_isProp(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_333; 
x_319 = lean_ctor_get(x_318, 0);
x_333 = !lean_is_exclusive(x_318);
if (x_333 == 0)
{
x_320 = x_318;
x_321 = x_333;
goto block_332;
}
else
{
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_box(0);
x_321 = x_333;
goto block_332;
}
block_332:
{
uint8_t x_322; 
x_322 = lean_unbox(x_319);
lean_dec(x_319);
if (x_322 == 0)
{
lean_del_object(x_320);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_323 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
x_324 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__21, &l_Lean_Meta_Grind_simpForall___closed__21_once, _init_l_Lean_Meta_Grind_simpForall___closed__21);
x_325 = l_Lean_Expr_app___override(x_324, x_14);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_327, 0, x_323);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set_uint8(x_327, sizeof(void*)*2, x_228);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_327);
if (x_321 == 0)
{
lean_ctor_set(x_320, 0, x_328);
x_329 = x_320;
goto block_330;
}
else
{
lean_object* x_331; 
x_331 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_331, 0, x_328);
x_329 = x_331;
goto block_330;
}
block_330:
{
return x_329;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; uint8_t x_341; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_334 = lean_ctor_get(x_318, 0);
x_341 = !lean_is_exclusive(x_318);
if (x_341 == 0)
{
x_335 = x_318;
x_336 = x_341;
goto block_340;
}
else
{
lean_inc(x_334);
lean_dec(x_318);
x_335 = lean_box(0);
x_336 = x_341;
goto block_340;
}
block_340:
{
lean_object* x_337; 
if (x_336 == 0)
{
x_337 = x_335;
goto block_338;
}
else
{
lean_object* x_339; 
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_334);
x_337 = x_339;
goto block_338;
}
block_338:
{
return x_337;
}
}
}
}
}
else
{
lean_object* x_342; 
lean_dec_ref(x_311);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
x_342 = l_Lean_Meta_isProp(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; uint8_t x_345; uint8_t x_357; 
x_343 = lean_ctor_get(x_342, 0);
x_357 = !lean_is_exclusive(x_342);
if (x_357 == 0)
{
x_344 = x_342;
x_345 = x_357;
goto block_356;
}
else
{
lean_inc(x_343);
lean_dec(x_342);
x_344 = lean_box(0);
x_345 = x_357;
goto block_356;
}
block_356:
{
uint8_t x_346; 
x_346 = lean_unbox(x_343);
lean_dec(x_343);
if (x_346 == 0)
{
lean_del_object(x_344);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_14);
x_347 = l_Lean_mkNot(x_14);
x_348 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__24, &l_Lean_Meta_Grind_simpForall___closed__24_once, _init_l_Lean_Meta_Grind_simpForall___closed__24);
x_349 = l_Lean_Expr_app___override(x_348, x_14);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
x_351 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*2, x_228);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
if (x_345 == 0)
{
lean_ctor_set(x_344, 0, x_352);
x_353 = x_344;
goto block_354;
}
else
{
lean_object* x_355; 
x_355 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_355, 0, x_352);
x_353 = x_355;
goto block_354;
}
block_354:
{
return x_353;
}
}
}
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; uint8_t x_365; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_358 = lean_ctor_get(x_342, 0);
x_365 = !lean_is_exclusive(x_342);
if (x_365 == 0)
{
x_359 = x_342;
x_360 = x_365;
goto block_364;
}
else
{
lean_inc(x_358);
lean_dec(x_342);
x_359 = lean_box(0);
x_360 = x_365;
goto block_364;
}
block_364:
{
lean_object* x_361; 
if (x_360 == 0)
{
x_361 = x_359;
goto block_362;
}
else
{
lean_object* x_363; 
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_358);
x_361 = x_363;
goto block_362;
}
block_362:
{
return x_361;
}
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; uint8_t x_373; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_366 = lean_ctor_get(x_309, 0);
x_373 = !lean_is_exclusive(x_309);
if (x_373 == 0)
{
x_367 = x_309;
x_368 = x_373;
goto block_372;
}
else
{
lean_inc(x_366);
lean_dec(x_309);
x_367 = lean_box(0);
x_368 = x_373;
goto block_372;
}
block_372:
{
lean_object* x_369; 
if (x_368 == 0)
{
x_369 = x_367;
goto block_370;
}
else
{
lean_object* x_371; 
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_366);
x_369 = x_371;
goto block_370;
}
block_370:
{
return x_369;
}
}
}
}
}
else
{
lean_object* x_374; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_374 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; uint8_t x_388; 
x_375 = lean_ctor_get(x_374, 0);
x_388 = !lean_is_exclusive(x_374);
if (x_388 == 0)
{
x_376 = x_374;
x_377 = x_388;
goto block_387;
}
else
{
lean_inc(x_375);
lean_dec(x_374);
x_376 = lean_box(0);
x_377 = x_388;
goto block_387;
}
block_387:
{
uint8_t x_378; 
x_378 = lean_unbox(x_375);
lean_dec(x_375);
if (x_378 == 0)
{
lean_del_object(x_376);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_379 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__27, &l_Lean_Meta_Grind_simpForall___closed__27_once, _init_l_Lean_Meta_Grind_simpForall___closed__27);
lean_inc_ref(x_15);
x_380 = l_Lean_Expr_app___override(x_379, x_15);
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_380);
x_382 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_382, 0, x_15);
lean_ctor_set(x_382, 1, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*2, x_228);
x_383 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_383, 0, x_382);
if (x_377 == 0)
{
lean_ctor_set(x_376, 0, x_383);
x_384 = x_376;
goto block_385;
}
else
{
lean_object* x_386; 
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_383);
x_384 = x_386;
goto block_385;
}
block_385:
{
return x_384;
}
}
}
}
else
{
lean_object* x_389; lean_object* x_390; uint8_t x_391; uint8_t x_396; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_389 = lean_ctor_get(x_374, 0);
x_396 = !lean_is_exclusive(x_374);
if (x_396 == 0)
{
x_390 = x_374;
x_391 = x_396;
goto block_395;
}
else
{
lean_inc(x_389);
lean_dec(x_374);
x_390 = lean_box(0);
x_391 = x_396;
goto block_395;
}
block_395:
{
lean_object* x_392; 
if (x_391 == 0)
{
x_392 = x_390;
goto block_393;
}
else
{
lean_object* x_394; 
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_389);
x_392 = x_394;
goto block_393;
}
block_393:
{
return x_392;
}
}
}
}
}
else
{
lean_object* x_397; 
lean_dec_ref(x_254);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_397 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; uint8_t x_400; uint8_t x_412; 
x_398 = lean_ctor_get(x_397, 0);
x_412 = !lean_is_exclusive(x_397);
if (x_412 == 0)
{
x_399 = x_397;
x_400 = x_412;
goto block_411;
}
else
{
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_box(0);
x_400 = x_412;
goto block_411;
}
block_411:
{
uint8_t x_401; 
x_401 = lean_unbox(x_398);
lean_dec(x_398);
if (x_401 == 0)
{
lean_del_object(x_399);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_402 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
x_403 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__30, &l_Lean_Meta_Grind_simpForall___closed__30_once, _init_l_Lean_Meta_Grind_simpForall___closed__30);
x_404 = l_Lean_Expr_app___override(x_403, x_15);
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_406 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set_uint8(x_406, sizeof(void*)*2, x_228);
x_407 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_407, 0, x_406);
if (x_400 == 0)
{
lean_ctor_set(x_399, 0, x_407);
x_408 = x_399;
goto block_409;
}
else
{
lean_object* x_410; 
x_410 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_410, 0, x_407);
x_408 = x_410;
goto block_409;
}
block_409:
{
return x_408;
}
}
}
}
else
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_420; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_413 = lean_ctor_get(x_397, 0);
x_420 = !lean_is_exclusive(x_397);
if (x_420 == 0)
{
x_414 = x_397;
x_415 = x_420;
goto block_419;
}
else
{
lean_inc(x_413);
lean_dec(x_397);
x_414 = lean_box(0);
x_415 = x_420;
goto block_419;
}
block_419:
{
lean_object* x_416; 
if (x_415 == 0)
{
x_416 = x_414;
goto block_417;
}
else
{
lean_object* x_418; 
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_413);
x_416 = x_418;
goto block_417;
}
block_417:
{
return x_416;
}
}
}
}
block_253:
{
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_244; 
x_230 = lean_ctor_get(x_229, 0);
x_244 = !lean_is_exclusive(x_229);
if (x_244 == 0)
{
x_231 = x_229;
x_232 = x_244;
goto block_243;
}
else
{
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_box(0);
x_232 = x_244;
goto block_243;
}
block_243:
{
uint8_t x_233; 
x_233 = lean_unbox(x_230);
lean_dec(x_230);
if (x_233 == 0)
{
lean_del_object(x_231);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_234 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
x_235 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__16, &l_Lean_Meta_Grind_simpForall___closed__16_once, _init_l_Lean_Meta_Grind_simpForall___closed__16);
x_236 = l_Lean_Expr_app___override(x_235, x_14);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set_uint8(x_238, sizeof(void*)*2, x_228);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_238);
if (x_232 == 0)
{
lean_ctor_set(x_231, 0, x_239);
x_240 = x_231;
goto block_241;
}
else
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_239);
x_240 = x_242;
goto block_241;
}
block_241:
{
return x_240;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_252; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_245 = lean_ctor_get(x_229, 0);
x_252 = !lean_is_exclusive(x_229);
if (x_252 == 0)
{
x_246 = x_229;
x_247 = x_252;
goto block_251;
}
else
{
lean_inc(x_245);
lean_dec(x_229);
x_246 = lean_box(0);
x_247 = x_252;
goto block_251;
}
block_251:
{
lean_object* x_248; 
if (x_247 == 0)
{
x_248 = x_246;
goto block_249;
}
else
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_245);
x_248 = x_250;
goto block_249;
}
block_249:
{
return x_248;
}
}
}
}
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; uint8_t x_428; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_421 = lean_ctor_get(x_226, 0);
x_428 = !lean_is_exclusive(x_226);
if (x_428 == 0)
{
x_422 = x_226;
x_423 = x_428;
goto block_427;
}
else
{
lean_inc(x_421);
lean_dec(x_226);
x_422 = lean_box(0);
x_423 = x_428;
goto block_427;
}
block_427:
{
lean_object* x_424; 
if (x_423 == 0)
{
x_424 = x_422;
goto block_425;
}
else
{
lean_object* x_426; 
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_421);
x_424 = x_426;
goto block_425;
}
block_425:
{
return x_424;
}
}
}
}
else
{
lean_object* x_429; 
lean_inc_ref(x_14);
x_429 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_14, x_6);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
lean_dec_ref(x_429);
x_431 = l_Lean_Expr_cleanupAnnotations(x_430);
x_432 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
x_433 = l_Lean_Expr_isConstOf(x_431, x_432);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
x_435 = l_Lean_Expr_isConstOf(x_431, x_434);
lean_dec_ref(x_431);
if (x_435 == 0)
{
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__33, &l_Lean_Meta_Grind_simpForall___closed__33_once, _init_l_Lean_Meta_Grind_simpForall___closed__33);
x_437 = lean_expr_instantiate1(x_15, x_436);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_437);
x_438 = l_Lean_Meta_isProp(x_437, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; uint8_t x_441; uint8_t x_453; 
x_439 = lean_ctor_get(x_438, 0);
x_453 = !lean_is_exclusive(x_438);
if (x_453 == 0)
{
x_440 = x_438;
x_441 = x_453;
goto block_452;
}
else
{
lean_inc(x_439);
lean_dec(x_438);
x_440 = lean_box(0);
x_441 = x_453;
goto block_452;
}
block_452:
{
uint8_t x_442; 
x_442 = lean_unbox(x_439);
lean_dec(x_439);
if (x_442 == 0)
{
lean_del_object(x_440);
lean_dec_ref(x_437);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_443 = l_Lean_mkLambda(x_13, x_16, x_14, x_15);
x_444 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__36, &l_Lean_Meta_Grind_simpForall___closed__36_once, _init_l_Lean_Meta_Grind_simpForall___closed__36);
x_445 = l_Lean_Expr_app___override(x_444, x_443);
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_447 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_447, 0, x_437);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_225);
x_448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_448, 0, x_447);
if (x_441 == 0)
{
lean_ctor_set(x_440, 0, x_448);
x_449 = x_440;
goto block_450;
}
else
{
lean_object* x_451; 
x_451 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_451, 0, x_448);
x_449 = x_451;
goto block_450;
}
block_450:
{
return x_449;
}
}
}
}
else
{
lean_object* x_454; lean_object* x_455; uint8_t x_456; uint8_t x_461; 
lean_dec_ref(x_437);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_454 = lean_ctor_get(x_438, 0);
x_461 = !lean_is_exclusive(x_438);
if (x_461 == 0)
{
x_455 = x_438;
x_456 = x_461;
goto block_460;
}
else
{
lean_inc(x_454);
lean_dec(x_438);
x_455 = lean_box(0);
x_456 = x_461;
goto block_460;
}
block_460:
{
lean_object* x_457; 
if (x_456 == 0)
{
x_457 = x_455;
goto block_458;
}
else
{
lean_object* x_459; 
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_454);
x_457 = x_459;
goto block_458;
}
block_458:
{
return x_457;
}
}
}
}
}
else
{
lean_object* x_462; lean_object* x_463; 
lean_dec_ref(x_431);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
x_462 = l_Lean_mkLambda(x_13, x_16, x_14, x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_462);
x_463 = lean_infer_type(x_462, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec_ref(x_463);
x_465 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__38, &l_Lean_Meta_Grind_simpForall___closed__38_once, _init_l_Lean_Meta_Grind_simpForall___closed__38);
lean_inc_ref(x_14);
lean_inc(x_13);
x_466 = l_Lean_mkForall(x_13, x_16, x_14, x_465);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_467 = l_Lean_Meta_isExprDefEq(x_464, x_466, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; uint8_t x_470; uint8_t x_482; 
x_468 = lean_ctor_get(x_467, 0);
x_482 = !lean_is_exclusive(x_467);
if (x_482 == 0)
{
x_469 = x_467;
x_470 = x_482;
goto block_481;
}
else
{
lean_inc(x_468);
lean_dec(x_467);
x_469 = lean_box(0);
x_470 = x_482;
goto block_481;
}
block_481:
{
uint8_t x_471; 
x_471 = lean_unbox(x_468);
lean_dec(x_468);
if (x_471 == 0)
{
lean_del_object(x_469);
lean_dec_ref(x_462);
x_213 = x_2;
x_214 = x_3;
x_215 = x_4;
x_216 = x_5;
x_217 = x_6;
x_218 = x_7;
x_219 = x_8;
goto block_224;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_472 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
x_473 = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__41, &l_Lean_Meta_Grind_simpForall___closed__41_once, _init_l_Lean_Meta_Grind_simpForall___closed__41);
x_474 = l_Lean_Expr_app___override(x_473, x_462);
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_474);
x_476 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_476, 0, x_472);
lean_ctor_set(x_476, 1, x_475);
lean_ctor_set_uint8(x_476, sizeof(void*)*2, x_225);
x_477 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_477, 0, x_476);
if (x_470 == 0)
{
lean_ctor_set(x_469, 0, x_477);
x_478 = x_469;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_480, 0, x_477);
x_478 = x_480;
goto block_479;
}
block_479:
{
return x_478;
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_490; 
lean_dec_ref(x_462);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_483 = lean_ctor_get(x_467, 0);
x_490 = !lean_is_exclusive(x_467);
if (x_490 == 0)
{
x_484 = x_467;
x_485 = x_490;
goto block_489;
}
else
{
lean_inc(x_483);
lean_dec(x_467);
x_484 = lean_box(0);
x_485 = x_490;
goto block_489;
}
block_489:
{
lean_object* x_486; 
if (x_485 == 0)
{
x_486 = x_484;
goto block_487;
}
else
{
lean_object* x_488; 
x_488 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_488, 0, x_483);
x_486 = x_488;
goto block_487;
}
block_487:
{
return x_486;
}
}
}
}
else
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; uint8_t x_498; 
lean_dec_ref(x_462);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_491 = lean_ctor_get(x_463, 0);
x_498 = !lean_is_exclusive(x_463);
if (x_498 == 0)
{
x_492 = x_463;
x_493 = x_498;
goto block_497;
}
else
{
lean_inc(x_491);
lean_dec(x_463);
x_492 = lean_box(0);
x_493 = x_498;
goto block_497;
}
block_497:
{
lean_object* x_494; 
if (x_493 == 0)
{
x_494 = x_492;
goto block_495;
}
else
{
lean_object* x_496; 
x_496 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_496, 0, x_491);
x_494 = x_496;
goto block_495;
}
block_495:
{
return x_494;
}
}
}
}
}
else
{
lean_object* x_499; lean_object* x_500; uint8_t x_501; uint8_t x_506; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_499 = lean_ctor_get(x_429, 0);
x_506 = !lean_is_exclusive(x_429);
if (x_506 == 0)
{
x_500 = x_429;
x_501 = x_506;
goto block_505;
}
else
{
lean_inc(x_499);
lean_dec(x_429);
x_500 = lean_box(0);
x_501 = x_506;
goto block_505;
}
block_505:
{
lean_object* x_502; 
if (x_501 == 0)
{
x_502 = x_500;
goto block_503;
}
else
{
lean_object* x_504; 
x_504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_504, 0, x_499);
x_502 = x_504;
goto block_503;
}
block_503:
{
return x_502;
}
}
}
}
block_212:
{
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Expr_appFn_x21(x_15);
x_26 = l_Lean_Expr_appFn_x21(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
x_29 = lean_name_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
x_31 = lean_name_eq(x_27, x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
goto block_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = l_Lean_Expr_appArg_x21(x_25);
lean_dec_ref(x_25);
x_33 = l_Lean_Expr_appArg_x21(x_15);
lean_dec_ref(x_15);
lean_inc_ref(x_32);
lean_inc_ref(x_14);
lean_inc(x_13);
x_34 = l_Lean_mkLambda(x_13, x_16, x_14, x_32);
lean_inc_ref(x_33);
lean_inc_ref(x_14);
lean_inc(x_13);
x_35 = l_Lean_mkLambda(x_13, x_16, x_14, x_33);
lean_inc_ref(x_14);
lean_inc(x_13);
x_36 = l_Lean_mkForall(x_13, x_16, x_14, x_32);
lean_inc_ref(x_14);
x_37 = l_Lean_mkForall(x_13, x_16, x_14, x_33);
lean_inc_ref(x_14);
x_38 = l_Lean_Meta_getLevel(x_14, x_22, x_21, x_23, x_18);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_55; 
x_39 = lean_ctor_get(x_38, 0);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
x_40 = x_38;
x_41 = x_55;
goto block_54;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = l_Lean_mkAnd(x_36, x_37);
x_43 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__6));
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_mkConst(x_43, x_45);
x_47 = l_Lean_mkApp3(x_46, x_14, x_34, x_35);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_24);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_50);
x_51 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_14);
x_56 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_57 = x_38;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_38);
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
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_27);
x_64 = l_Lean_Expr_appArg_x21(x_25);
lean_dec_ref(x_25);
x_65 = l_Lean_Expr_appArg_x21(x_15);
lean_dec_ref(x_15);
x_66 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_64);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_137; 
lean_dec_ref(x_64);
x_67 = lean_ctor_get(x_66, 0);
x_137 = !lean_is_exclusive(x_66);
if (x_137 == 0)
{
x_68 = x_66;
x_69 = x_137;
goto block_136;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_135; 
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_ctor_get(x_67, 0);
x_135 = !lean_is_exclusive(x_67);
if (x_135 == 0)
{
x_72 = x_67;
x_73 = x_135;
goto block_134;
}
else
{
lean_inc(x_70);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_box(0);
x_73 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_133; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
x_133 = !lean_is_exclusive(x_70);
if (x_133 == 0)
{
x_76 = x_70;
x_77 = x_133;
goto block_132;
}
else
{
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_box(0);
x_77 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc_ref(x_65);
lean_inc_ref(x_14);
lean_inc(x_13);
x_78 = l_Lean_mkLambda(x_13, x_16, x_14, x_65);
x_79 = 0;
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_71);
x_80 = l_Lean_mkLambda(x_71, x_79, x_74, x_75);
lean_inc_ref(x_14);
lean_inc(x_13);
x_81 = l_Lean_mkLambda(x_13, x_16, x_14, x_80);
lean_inc(x_74);
lean_inc_ref(x_14);
lean_inc(x_13);
x_82 = l_Lean_mkLambda(x_13, x_16, x_14, x_74);
lean_inc(x_18);
lean_inc_ref(x_23);
lean_inc(x_21);
lean_inc_ref(x_22);
lean_inc_ref(x_14);
x_83 = l_Lean_Meta_getLevel(x_14, x_22, x_21, x_23, x_18);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_74);
x_85 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_85, 0, x_74);
lean_inc_ref(x_14);
lean_inc(x_13);
x_86 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_13, x_14, x_85, x_17, x_20, x_19, x_22, x_21, x_23, x_18);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_115; 
x_87 = lean_ctor_get(x_86, 0);
x_115 = !lean_is_exclusive(x_86);
if (x_115 == 0)
{
x_88 = x_86;
x_89 = x_115;
goto block_114;
}
else
{
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_box(0);
x_89 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_expr_lift_loose_bvars(x_65, x_90, x_91);
lean_dec_ref(x_65);
x_93 = l_Lean_mkOr(x_75, x_92);
x_94 = l_Lean_mkForall(x_71, x_79, x_74, x_93);
lean_inc_ref(x_14);
x_95 = l_Lean_mkForall(x_13, x_16, x_14, x_94);
x_96 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
x_97 = lean_box(0);
if (x_77 == 0)
{
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 1, x_97);
lean_ctor_set(x_76, 0, x_87);
x_98 = x_76;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_87);
lean_ctor_set(x_113, 1, x_97);
x_98 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_99; 
if (x_73 == 0)
{
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_98);
lean_ctor_set(x_72, 0, x_84);
x_99 = x_72;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_84);
lean_ctor_set(x_111, 1, x_98);
x_99 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = l_Lean_mkConst(x_96, x_99);
x_101 = l_Lean_mkApp4(x_100, x_14, x_82, x_78, x_81);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_101);
x_102 = x_68;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_101);
x_102 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_103, 0, x_95);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_24);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
if (x_89 == 0)
{
lean_ctor_set(x_88, 0, x_104);
x_105 = x_88;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_104);
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
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec(x_84);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_78);
lean_del_object(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_del_object(x_72);
lean_dec(x_71);
lean_del_object(x_68);
lean_dec_ref(x_65);
lean_dec_ref(x_14);
lean_dec(x_13);
x_116 = lean_ctor_get(x_86, 0);
x_123 = !lean_is_exclusive(x_86);
if (x_123 == 0)
{
x_117 = x_86;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_86);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_78);
lean_del_object(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_del_object(x_72);
lean_dec(x_71);
lean_del_object(x_68);
lean_dec_ref(x_65);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_13);
x_124 = lean_ctor_get(x_83, 0);
x_131 = !lean_is_exclusive(x_83);
if (x_131 == 0)
{
x_125 = x_83;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_dec(x_83);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_124);
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
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_66);
x_138 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_65);
lean_dec_ref(x_65);
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_209; 
x_139 = lean_ctor_get(x_138, 0);
x_209 = !lean_is_exclusive(x_138);
if (x_209 == 0)
{
x_140 = x_138;
x_141 = x_209;
goto block_208;
}
else
{
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_box(0);
x_141 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_207; 
x_142 = lean_ctor_get(x_139, 1);
x_143 = lean_ctor_get(x_139, 0);
x_207 = !lean_is_exclusive(x_139);
if (x_207 == 0)
{
x_144 = x_139;
x_145 = x_207;
goto block_206;
}
else
{
lean_inc(x_142);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_box(0);
x_145 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_205; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
x_205 = !lean_is_exclusive(x_142);
if (x_205 == 0)
{
x_148 = x_142;
x_149 = x_205;
goto block_204;
}
else
{
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_box(0);
x_149 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_inc_ref(x_64);
lean_inc_ref(x_14);
lean_inc(x_13);
x_150 = l_Lean_mkLambda(x_13, x_16, x_14, x_64);
x_151 = 0;
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_143);
x_152 = l_Lean_mkLambda(x_143, x_151, x_146, x_147);
lean_inc_ref(x_14);
lean_inc(x_13);
x_153 = l_Lean_mkLambda(x_13, x_16, x_14, x_152);
lean_inc(x_146);
lean_inc_ref(x_14);
lean_inc(x_13);
x_154 = l_Lean_mkLambda(x_13, x_16, x_14, x_146);
lean_inc(x_18);
lean_inc_ref(x_23);
lean_inc(x_21);
lean_inc_ref(x_22);
lean_inc_ref(x_14);
x_155 = l_Lean_Meta_getLevel(x_14, x_22, x_21, x_23, x_18);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
lean_inc(x_146);
x_157 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_157, 0, x_146);
lean_inc_ref(x_14);
lean_inc(x_13);
x_158 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_13, x_14, x_157, x_17, x_20, x_19, x_22, x_21, x_23, x_18);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_187; 
x_159 = lean_ctor_get(x_158, 0);
x_187 = !lean_is_exclusive(x_158);
if (x_187 == 0)
{
x_160 = x_158;
x_161 = x_187;
goto block_186;
}
else
{
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_box(0);
x_161 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_expr_lift_loose_bvars(x_64, x_162, x_163);
lean_dec_ref(x_64);
x_165 = l_Lean_mkOr(x_164, x_147);
x_166 = l_Lean_mkForall(x_143, x_151, x_146, x_165);
lean_inc_ref(x_14);
x_167 = l_Lean_mkForall(x_13, x_16, x_14, x_166);
x_168 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__10));
x_169 = lean_box(0);
if (x_149 == 0)
{
lean_ctor_set_tag(x_148, 1);
lean_ctor_set(x_148, 1, x_169);
lean_ctor_set(x_148, 0, x_159);
x_170 = x_148;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_159);
lean_ctor_set(x_185, 1, x_169);
x_170 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_171; 
if (x_145 == 0)
{
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 1, x_170);
lean_ctor_set(x_144, 0, x_156);
x_171 = x_144;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_156);
lean_ctor_set(x_183, 1, x_170);
x_171 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = l_Lean_mkConst(x_168, x_171);
x_173 = l_Lean_mkApp4(x_172, x_14, x_154, x_150, x_153);
if (x_141 == 0)
{
lean_ctor_set(x_140, 0, x_173);
x_174 = x_140;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_173);
x_174 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*2, x_24);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
if (x_161 == 0)
{
lean_ctor_set(x_160, 0, x_176);
x_177 = x_160;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_176);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_195; 
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_150);
lean_del_object(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_del_object(x_144);
lean_dec(x_143);
lean_del_object(x_140);
lean_dec_ref(x_64);
lean_dec_ref(x_14);
lean_dec(x_13);
x_188 = lean_ctor_get(x_158, 0);
x_195 = !lean_is_exclusive(x_158);
if (x_195 == 0)
{
x_189 = x_158;
x_190 = x_195;
goto block_194;
}
else
{
lean_inc(x_188);
lean_dec(x_158);
x_189 = lean_box(0);
x_190 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_191; 
if (x_190 == 0)
{
x_191 = x_189;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_188);
x_191 = x_193;
goto block_192;
}
block_192:
{
return x_191;
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_203; 
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_150);
lean_del_object(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_del_object(x_144);
lean_dec(x_143);
lean_del_object(x_140);
lean_dec_ref(x_64);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_13);
x_196 = lean_ctor_get(x_155, 0);
x_203 = !lean_is_exclusive(x_155);
if (x_203 == 0)
{
x_197 = x_155;
x_198 = x_203;
goto block_202;
}
else
{
lean_inc(x_196);
lean_dec(x_155);
x_197 = lean_box(0);
x_198 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_199; 
if (x_198 == 0)
{
x_199 = x_197;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_196);
x_199 = x_201;
goto block_200;
}
block_200:
{
return x_199;
}
}
}
}
}
}
}
else
{
lean_dec(x_138);
lean_dec_ref(x_64);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_13);
goto block_12;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
x_210 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
}
block_224:
{
uint8_t x_220; 
x_220 = l_Lean_Expr_isApp(x_15);
if (x_220 == 0)
{
x_17 = x_213;
x_18 = x_219;
x_19 = x_215;
x_20 = x_214;
x_21 = x_217;
x_22 = x_216;
x_23 = x_218;
x_24 = x_220;
goto block_212;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = l_Lean_Expr_getAppNumArgs(x_15);
x_222 = lean_unsigned_to_nat(2u);
x_223 = lean_nat_dec_eq(x_221, x_222);
lean_dec(x_221);
x_17 = x_213;
x_18 = x_219;
x_19 = x_215;
x_20 = x_214;
x_21 = x_217;
x_22 = x_216;
x_23 = x_218;
x_24 = x_223;
goto block_212;
}
}
}
else
{
lean_object* x_507; lean_object* x_508; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_507 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_508 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_508, 0, x_507);
return x_508;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_));
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_cleanupAnnotations(x_1);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__5));
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_9;
}
else
{
if (lean_obj_tag(x_15) == 6)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_118; uint8_t x_148; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_15);
x_148 = l_Lean_Expr_isApp(x_23);
if (x_148 == 0)
{
x_118 = x_148;
goto block_147;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = l_Lean_Expr_getAppNumArgs(x_23);
x_150 = lean_unsigned_to_nat(2u);
x_151 = lean_nat_dec_eq(x_149, x_150);
lean_dec(x_149);
x_118 = x_151;
goto block_147;
}
block_87:
{
uint8_t x_28; 
x_28 = l_Lean_Expr_hasLooseBVars(x_23);
if (x_28 == 0)
{
if (x_21 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
goto block_12;
}
else
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc_ref(x_18);
x_29 = l_Lean_Meta_isProp(x_18, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_78; 
x_30 = lean_ctor_get(x_29, 0);
x_78 = !lean_is_exclusive(x_29);
if (x_78 == 0)
{
x_31 = x_29;
x_32 = x_78;
goto block_77;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_78;
goto block_77;
}
block_77:
{
uint8_t x_33; 
x_33 = lean_unbox(x_30);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_del_object(x_31);
x_34 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_35 = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__1));
lean_inc(x_34);
x_36 = l_Lean_mkConst(x_35, x_34);
lean_inc_ref(x_18);
x_37 = l_Lean_Expr_app___override(x_36, x_18);
x_38 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_37, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_59; 
x_39 = lean_ctor_get(x_38, 0);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
x_40 = x_38;
x_41 = x_59;
goto block_58;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_59;
goto block_58;
}
block_58:
{
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_57; 
x_42 = lean_ctor_get(x_39, 0);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
x_43 = x_39;
x_44 = x_57;
goto block_56;
}
else
{
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__3));
x_46 = l_Lean_mkConst(x_45, x_34);
lean_inc_ref(x_23);
x_47 = l_Lean_mkApp3(x_46, x_18, x_42, x_23);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_47);
x_48 = x_43;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_47);
x_48 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_21);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_50);
x_51 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
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
lean_del_object(x_40);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
goto block_12;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_34);
lean_dec_ref(x_23);
lean_dec_ref(x_18);
x_60 = lean_ctor_get(x_38, 0);
x_67 = !lean_is_exclusive(x_38);
if (x_67 == 0)
{
x_61 = x_38;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
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
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_inc_ref(x_23);
lean_inc_ref(x_18);
x_68 = l_Lean_mkAnd(x_18, x_23);
x_69 = lean_obj_once(&l_Lean_Meta_Grind_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6);
x_70 = l_Lean_mkAppB(x_69, x_18, x_23);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_21);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_73);
x_74 = x_31;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
x_79 = lean_ctor_get(x_29, 0);
x_86 = !lean_is_exclusive(x_29);
if (x_86 == 0)
{
x_80 = x_29;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_29);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
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
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
goto block_12;
}
}
block_117:
{
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Expr_hasLooseBVars(x_90);
if (x_92 == 0)
{
if (x_88 == 0)
{
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec(x_22);
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_87;
}
else
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_23);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_93 = 0;
lean_inc_ref(x_18);
x_94 = l_Lean_mkLambda(x_22, x_93, x_18, x_89);
lean_inc_ref(x_94);
lean_inc_ref(x_18);
lean_inc_ref(x_19);
x_95 = l_Lean_mkAppB(x_19, x_18, x_94);
lean_inc_ref(x_90);
x_96 = l_Lean_mkAnd(x_95, x_90);
x_97 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_98 = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__8));
x_99 = l_Lean_mkConst(x_98, x_97);
x_100 = l_Lean_mkApp3(x_99, x_18, x_94, x_90);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_21);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
else
{
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec(x_22);
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_87;
}
}
else
{
uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_23);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = 0;
lean_inc_ref(x_18);
x_106 = l_Lean_mkLambda(x_22, x_105, x_18, x_90);
lean_inc_ref(x_106);
lean_inc_ref(x_18);
lean_inc_ref(x_19);
x_107 = l_Lean_mkAppB(x_19, x_18, x_106);
lean_inc_ref(x_89);
x_108 = l_Lean_mkAnd(x_89, x_107);
x_109 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_110 = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__10));
x_111 = l_Lean_mkConst(x_110, x_109);
x_112 = l_Lean_mkApp3(x_111, x_18, x_106, x_89);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_21);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
block_147:
{
if (x_118 == 0)
{
lean_dec(x_22);
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_87;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Expr_appFn_x21(x_23);
x_120 = l_Lean_Expr_appFn_x21(x_119);
if (lean_obj_tag(x_120) == 4)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
x_123 = lean_name_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
x_125 = lean_name_eq(x_121, x_124);
lean_dec(x_121);
if (x_125 == 0)
{
lean_dec_ref(x_119);
lean_dec(x_22);
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_87;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = l_Lean_Expr_appArg_x21(x_119);
lean_dec_ref(x_119);
x_127 = l_Lean_Expr_appArg_x21(x_23);
x_128 = l_Lean_Expr_hasLooseBVars(x_126);
if (x_128 == 0)
{
x_88 = x_125;
x_89 = x_126;
x_90 = x_127;
x_91 = x_125;
goto block_117;
}
else
{
x_88 = x_125;
x_89 = x_126;
x_90 = x_127;
x_91 = x_123;
goto block_117;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_121);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_129 = l_Lean_Expr_appArg_x21(x_119);
lean_dec_ref(x_119);
x_130 = l_Lean_Expr_appArg_x21(x_23);
lean_dec_ref(x_23);
x_131 = 0;
lean_inc_ref(x_18);
lean_inc(x_22);
x_132 = l_Lean_mkLambda(x_22, x_131, x_18, x_129);
lean_inc_ref(x_18);
x_133 = l_Lean_mkLambda(x_22, x_131, x_18, x_130);
x_134 = l_Lean_Expr_constLevels_x21(x_19);
lean_inc_ref(x_132);
lean_inc_ref(x_18);
lean_inc_ref(x_19);
x_135 = l_Lean_mkAppB(x_19, x_18, x_132);
lean_inc_ref(x_133);
lean_inc_ref(x_18);
x_136 = l_Lean_mkAppB(x_19, x_18, x_133);
x_137 = l_Lean_mkOr(x_135, x_136);
x_138 = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__12));
x_139 = l_Lean_mkConst(x_138, x_134);
x_140 = l_Lean_mkApp3(x_139, x_18, x_132, x_133);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_21);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_145 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_152 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_simpExists___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_));
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_));
x_6 = 1;
x_7 = l_Lean_Meta_Simp_Simprocs_add(x_1, x_5, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_));
x_10 = l_Lean_Meta_Simp_Simprocs_add(x_8, x_9, x_6, x_2, x_3);
return x_10;
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_addForallSimproc(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Propagator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Norm(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Propagator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
}
#ifdef __cplusplus
}
#endif
