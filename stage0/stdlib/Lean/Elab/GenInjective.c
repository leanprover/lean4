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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 64, 157, 104, 62, 24, 0, 194)}};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___boxed(lean_object*);
lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1_, v___x_2_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_n(v_a_11_, 2);
lean_dec_ref_known(v___x_10_, 1);
v___x_12_ = l_Lean_mkCtorIdx(v_a_11_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v___x_13_; 
lean_dec_ref_known(v___x_12_, 1);
v___x_13_ = l_Lean_Meta_mkInjectiveTheorems(v_a_11_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
return v___x_13_;
}
else
{
lean_dec(v_a_11_);
return v___x_12_;
}
}
else
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_a_14_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v___x_10_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_10_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v___x_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_22_;
v_res_22_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(v___x_1_, v___x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed(lean_object* v___x_23_, lean_object* v___x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(v___x_23_, v___x_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
return v_res_32_;
}
}
lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(lean_object* v_stx_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___f_40_; lean_object* v___x_41_; 
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = l_Lean_Syntax_getArg(v_stx_33_, v___x_37_);
v___x_39_ = lean_box(0);
v___f_40_ = lean_alloc_closure((void*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed), 9, 2);
lean_closure_set(v___f_40_, 0, v___x_38_);
lean_closure_set(v___f_40_, 1, v___x_39_);
v___x_41_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_40_, v_a_34_, v_a_35_);
return v___x_41_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_33_ = stack[0].m_obj;
lean_object* v_a_34_ = stack[1].m_obj;
lean_object* v_a_35_ = stack[2].m_obj;
lean_object* v_res_42_;
v_res_42_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(v_stx_33_, v_a_34_, v_a_35_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed(lean_object* v_stx_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(v_stx_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_stx_43_);
return v_res_47_;
}
}
lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1(){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_89_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_90_ = ((lean_object*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4));
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17));
v___x_92_ = lean_alloc_closure((void*)(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed), 4, 0);
v___x_93_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_89_, v___x_90_, v___x_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_94_;
v_res_94_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___boxed(lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
return v_res_96_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_GenInjective(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_GenInjective(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_GenInjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_GenInjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_GenInjective(builtin);
}
#ifdef __cplusplus
}
#endif
