// Lean compiler output
// Module: Lean.Elab.Tactic.SimpArith
// Imports: public import Lean.Elab.Tactic.Simp public import Lean.Meta.Tactic.TryThis
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__2_value;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10_value;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1_value;
static lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try these:"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__3_value;
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 164, .m_capacity = 164, .m_length = 163, .m_data = "`simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___closed__2_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpArith___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpArith"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 47, 198, 44, 197, 94, 244, 200)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpArith"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(57, 196, 188, 196, 176, 200, 33, 77)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simp!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 205, 236, 180, 188, 29, 173, 240)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 166, .m_capacity = 166, .m_length = 165, .m_data = "`simp_arith!` has been deprecated. It was a shorthand for `simp! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3_value;
static lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpArithBang"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 151, 237, 27, 117, 76, 215, 64)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalSimpArithBang"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(112, 207, 16, 1, 121, 65, 25, 137)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 172, .m_capacity = 172, .m_length = 171, .m_data = "`simp_all_arith` has been deprecated. It was a shorthand for `simp_all +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3_value;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpAllArith"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 202, 96, 76, 254, 39, 20, 47)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSimpAllArith"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 116, 46, 40, 95, 195, 237, 247)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simp_all!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 140, 78, 27, 53, 62, 238, 147)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 174, .m_capacity = 174, .m_length = 173, .m_data = "`simp_all_arith!` has been deprecated. It was a shorthand for `simp_all! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented."};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3_value;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpAllArithBang"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 196, 181, 251, 41, 107, 56, 49)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalSimpAllArithBang"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(224, 193, 22, 168, 77, 173, 215, 80)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___boxed(lean_object*);
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = l_Lean_Syntax_setArg(x_1, x_3, x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_4, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_array_fget(x_7, x_8);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_8, x_17);
x_19 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0;
x_20 = lean_array_push(x_19, x_2);
x_21 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_22 = l_Array_append___redArg(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__2));
x_24 = lean_box(2);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_24);
x_25 = lean_array_fset(x_18, x_8, x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_Syntax_setArg(x_1, x_3, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
x_28 = lean_array_fget(x_7, x_8);
x_29 = lean_box(0);
x_30 = lean_array_fset(x_7, x_8, x_29);
x_31 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0;
x_32 = lean_array_push(x_31, x_2);
x_33 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_34 = l_Array_append___redArg(x_32, x_33);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__2));
x_36 = lean_box(2);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_34);
x_38 = lean_array_fset(x_30, x_8, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_6);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_Syntax_setArg(x_1, x_3, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_2);
x_41 = l_Lean_Syntax_setArg(x_1, x_3, x_4);
return x_41;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = 0;
x_6 = l_Lean_SourceInfo_fromRef(x_4, x_5);
x_7 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4));
x_8 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6));
x_9 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7));
lean_inc(x_6);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9;
x_12 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10));
x_13 = lean_box(0);
lean_inc(x_6);
x_14 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_inc(x_6);
x_15 = l_Lean_Syntax_node2(x_6, x_8, x_10, x_14);
x_16 = l_Lean_Syntax_node1(x_6, x_7, x_15);
x_17 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(x_1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = 0;
x_6 = l_Lean_SourceInfo_fromRef(x_4, x_5);
x_7 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4));
x_8 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6));
x_9 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7));
lean_inc(x_6);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1;
x_12 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2));
x_13 = lean_box(0);
lean_inc(x_6);
x_14 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_inc(x_6);
x_15 = l_Lean_Syntax_node2(x_6, x_8, x_10, x_14);
x_16 = l_Lean_Syntax_node1(x_6, x_7, x_15);
x_17 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(x_1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Syntax_setKind(x_1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_mkAtom(x_2);
x_7 = l_Lean_Syntax_setArg(x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_7 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(x_1, x_2, x_3);
x_8 = l_Lean_Syntax_unsetTrailing(x_7);
lean_inc(x_8);
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(x_8, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(x_8, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(x_12, x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_4, 5);
x_17 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1));
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_15);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_21);
x_25 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2;
x_26 = lean_array_push(x_25, x_22);
x_27 = lean_array_push(x_26, x_24);
lean_inc(x_16);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
x_28 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__3));
x_29 = 4;
x_30 = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(x_19, x_27, x_13, x_28, x_21, x_29, x_4, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_4, 5);
x_33 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1));
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_37);
x_41 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2;
x_42 = lean_array_push(x_41, x_38);
x_43 = lean_array_push(x_42, x_40);
lean_inc(x_32);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_32);
x_45 = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__3));
x_46 = 4;
x_47 = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(x_35, x_43, x_44, x_45, x_37, x_46, x_4, x_5);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__0));
x_12 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__1));
lean_inc(x_9);
lean_inc_ref(x_8);
x_13 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(x_1, x_11, x_12, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = l_Lean_Elab_Tactic_evalSimpArith___closed__3;
x_15 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(x_14, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_15;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArith___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0));
x_8 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2));
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(x_1, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4;
x_11 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(x_10, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(x_1, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArithBang(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArithBang___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0));
x_8 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2));
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(x_1, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4;
x_11 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(x_10, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(x_1, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArith___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0));
x_8 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2));
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(x_1, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4;
x_11 = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(x_10, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(x_1, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArithBang(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_SimpArith(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0);
l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9 = _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9);
l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1);
l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2 = _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2);
l_Lean_Elab_Tactic_evalSimpArith___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpArith___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4);
if (builtin) {res = l_Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4);
if (builtin) {res = l_Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4);
if (builtin) {res = l_Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
