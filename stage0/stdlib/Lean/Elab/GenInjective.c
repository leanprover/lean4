// Lean compiler output
// Module: Lean.Elab.GenInjective
// Imports: public import Lean.Elab.Command import Lean.Meta.Injective import Lean.Meta.Constructions.CtorIdx
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
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "genInjectiveTheorems"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 64, 157, 104, 62, 24, 0, 194)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "GenInjective"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(170, 196, 141, 133, 178, 29, 107, 25)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(171, 172, 67, 166, 155, 138, 207, 218)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 248, 212, 13, 77, 188, 223, 123)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 88, 37, 183, 56, 195, 251, 29)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(33, 90, 148, 154, 207, 199, 77, 4)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "elabGenInjectiveTheorems"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(101, 223, 159, 188, 46, 129, 194, 136)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
x_10 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_11);
x_12 = l_mkCtorIdx(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = l_Lean_Meta_mkInjectiveTheorems(x_11, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed), 9, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Command_liftTermElabM___redArg(x_8, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4));
x_4 = ((lean_object*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_GenInjective(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
