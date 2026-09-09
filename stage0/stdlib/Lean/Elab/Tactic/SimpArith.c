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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value;
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try these:"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpArith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpArith___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpArith"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 47, 198, 44, 197, 94, 244, 200)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpArith"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(57, 196, 188, 196, 176, 200, 33, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpArithBang"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 151, 237, 27, 117, 76, 215, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalSimpArithBang"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(112, 207, 16, 1, 121, 65, 25, 137)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpAllArith"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 202, 96, 76, 254, 39, 20, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSimpAllArith"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 116, 46, 40, 95, 195, 237, 247)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpAllArithBang"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 196, 181, 251, 41, 107, 56, 49)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalSimpAllArithBang"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(224, 193, 22, 168, 77, 173, 215, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(lean_object* v_stx_4_, lean_object* v_item_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_optConfig_7_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v_optConfig_7_ = l_Lean_Syntax_getArg(v_stx_4_, v___x_6_);
if (lean_obj_tag(v_optConfig_7_) == 1)
{
lean_object* v_info_8_; lean_object* v_kind_9_; lean_object* v_args_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_info_8_ = lean_ctor_get(v_optConfig_7_, 0);
lean_inc(v_info_8_);
v_kind_9_ = lean_ctor_get(v_optConfig_7_, 1);
lean_inc(v_kind_9_);
v_args_10_ = lean_ctor_get(v_optConfig_7_, 2);
lean_inc_ref(v_args_10_);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_array_get_size(v_args_10_);
v___x_13_ = lean_nat_dec_lt(v___x_11_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec_ref(v_args_10_);
lean_dec(v_kind_9_);
lean_dec(v_info_8_);
lean_dec(v_item_5_);
v___x_14_ = l_Lean_Syntax_setArg(v_stx_4_, v___x_6_, v_optConfig_7_);
return v___x_14_;
}
else
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_33_; 
v_isSharedCheck_33_ = !lean_is_exclusive(v_optConfig_7_);
if (v_isSharedCheck_33_ == 0)
{
lean_object* v_unused_34_; lean_object* v_unused_35_; lean_object* v_unused_36_; 
v_unused_34_ = lean_ctor_get(v_optConfig_7_, 2);
lean_dec(v_unused_34_);
v_unused_35_ = lean_ctor_get(v_optConfig_7_, 1);
lean_dec(v_unused_35_);
v_unused_36_ = lean_ctor_get(v_optConfig_7_, 0);
lean_dec(v_unused_36_);
v___x_16_ = v_optConfig_7_;
v_isShared_17_ = v_isSharedCheck_33_;
goto v_resetjp_15_;
}
else
{
lean_dec(v_optConfig_7_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_33_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_v_18_; lean_object* v___x_19_; lean_object* v_xs_x27_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v_v_18_ = lean_array_fget(v_args_10_, v___x_11_);
v___x_19_ = lean_box(0);
v_xs_x27_20_ = lean_array_fset(v_args_10_, v___x_11_, v___x_19_);
v___x_21_ = lean_mk_empty_array_with_capacity(v___x_6_);
v___x_22_ = lean_array_push(v___x_21_, v_item_5_);
v___x_23_ = l_Lean_Syntax_getArgs(v_v_18_);
lean_dec(v_v_18_);
v___x_24_ = l_Array_append___redArg(v___x_22_, v___x_23_);
lean_dec_ref(v___x_23_);
v___x_25_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1));
v___x_26_ = lean_box(2);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 2, v___x_24_);
lean_ctor_set(v___x_16_, 1, v___x_25_);
lean_ctor_set(v___x_16_, 0, v___x_26_);
v___x_28_ = v___x_16_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_32_, 2, v___x_24_);
v___x_28_ = v_reuseFailAlloc_32_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_array_fset(v_xs_x27_20_, v___x_11_, v___x_28_);
v___x_30_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_30_, 0, v_info_8_);
lean_ctor_set(v___x_30_, 1, v_kind_9_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
v___x_31_ = l_Lean_Syntax_setArg(v_stx_4_, v___x_6_, v___x_30_);
return v___x_31_;
}
}
}
}
else
{
lean_object* v___x_37_; 
lean_dec(v_item_5_);
v___x_37_ = l_Lean_Syntax_setArg(v_stx_4_, v___x_6_, v_optConfig_7_);
return v___x_37_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8));
v___x_56_ = l_String_toRawSubstring_x27(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(lean_object* v_stx_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_ref_62_; uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_ref_62_ = lean_ctor_get(v_a_60_, 2);
v___x_63_ = 0;
v___x_64_ = l_Lean_SourceInfo_fromRef(v_ref_62_, v___x_63_);
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4));
v___x_66_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6));
v___x_67_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7));
lean_inc_n(v___x_64_, 3);
v___x_68_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_64_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_obj_once(&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9, &l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9);
v___x_70_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10));
v___x_71_ = lean_box(0);
v___x_72_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_72_, 0, v___x_64_);
lean_ctor_set(v___x_72_, 1, v___x_69_);
lean_ctor_set(v___x_72_, 2, v___x_70_);
lean_ctor_set(v___x_72_, 3, v___x_71_);
v___x_73_ = l_Lean_Syntax_node2(v___x_64_, v___x_66_, v___x_68_, v___x_72_);
v___x_74_ = l_Lean_Syntax_node1(v___x_64_, v___x_65_, v___x_73_);
v___x_75_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(v_stx_59_, v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___boxed(lean_object* v_stx_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_77_, v_a_78_);
lean_dec_ref(v_a_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object* v_stx_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_81_, v_a_82_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object* v_stx_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(v_stx_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_90_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0));
v___x_93_ = l_String_toRawSubstring_x27(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(lean_object* v_stx_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_ref_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_ref_99_ = lean_ctor_get(v_a_97_, 2);
v___x_100_ = 0;
v___x_101_ = l_Lean_SourceInfo_fromRef(v_ref_99_, v___x_100_);
v___x_102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4));
v___x_103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6));
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7));
lean_inc_n(v___x_101_, 3);
v___x_105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_101_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_obj_once(&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1, &l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1);
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2));
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_109_, 0, v___x_101_);
lean_ctor_set(v___x_109_, 1, v___x_106_);
lean_ctor_set(v___x_109_, 2, v___x_107_);
lean_ctor_set(v___x_109_, 3, v___x_108_);
v___x_110_ = l_Lean_Syntax_node2(v___x_101_, v___x_103_, v___x_105_, v___x_109_);
v___x_111_ = l_Lean_Syntax_node1(v___x_101_, v___x_102_, v___x_110_);
v___x_112_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(v_stx_96_, v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___boxed(lean_object* v_stx_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_114_, v_a_115_);
lean_dec_ref(v_a_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object* v_stx_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_118_, v_a_119_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object* v_stx_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(v_stx_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object* v_stx_128_, lean_object* v_str_129_, lean_object* v_kind_130_){
_start:
{
lean_object* v_stx_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_stx_131_ = l_Lean_Syntax_setKind(v_stx_128_, v_kind_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = l_Lean_mkAtom(v_str_129_);
v___x_134_ = l_Lean_Syntax_setArg(v_stx_131_, v___x_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(lean_object* v_stx_139_, lean_object* v_tokenNew_140_, lean_object* v_kindNew_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_stx_x27_145_; lean_object* v_stx_x27_146_; lean_object* v___x_147_; lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v_a_150_; lean_object* v___x_151_; lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_176_; 
lean_inc(v_stx_139_);
v_stx_x27_145_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(v_stx_139_, v_tokenNew_140_, v_kindNew_141_);
v_stx_x27_146_ = l_Lean_Syntax_unsetTrailing(v_stx_x27_145_);
lean_inc(v_stx_x27_146_);
v___x_147_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_x27_146_, v_a_142_);
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v___x_147_);
v___x_149_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_x27_146_, v_a_142_);
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref(v___x_149_);
v___x_151_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_a_150_, v_a_142_);
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_176_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_176_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_176_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v_ref_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v_ref_156_ = lean_ctor_get(v_a_142_, 2);
v___x_157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1));
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = l_Lean_Syntax_getArg(v_stx_139_, v___x_158_);
lean_dec(v_stx_139_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_157_);
lean_ctor_set(v___x_160_, 1, v_a_148_);
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
lean_ctor_set(v___x_162_, 2, v___x_161_);
lean_ctor_set(v___x_162_, 3, v___x_161_);
lean_ctor_set(v___x_162_, 4, v___x_161_);
lean_ctor_set(v___x_162_, 5, v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_157_);
lean_ctor_set(v___x_163_, 1, v_a_152_);
v___x_164_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_161_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
lean_ctor_set(v___x_164_, 3, v___x_161_);
lean_ctor_set(v___x_164_, 4, v___x_161_);
lean_ctor_set(v___x_164_, 5, v___x_161_);
v___x_165_ = lean_unsigned_to_nat(2u);
v___x_166_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_167_ = lean_array_push(v___x_166_, v___x_162_);
v___x_168_ = lean_array_push(v___x_167_, v___x_164_);
lean_inc(v_ref_156_);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 1);
lean_ctor_set(v___x_154_, 0, v_ref_156_);
v___x_170_ = v___x_154_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_ref_156_);
v___x_170_ = v_reuseFailAlloc_175_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2));
v___x_172_ = 4;
v___x_173_ = l_Lean_MessageData_nil;
v___x_174_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v___x_159_, v___x_168_, v___x_170_, v___x_171_, v___x_161_, v___x_172_, v___x_173_, v_a_142_, v_a_143_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___boxed(lean_object* v_stx_177_, lean_object* v_tokenNew_178_, lean_object* v_kindNew_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_177_, v_tokenNew_178_, v_kindNew_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object* v_stx_184_, lean_object* v_tokenNew_185_, lean_object* v_kindNew_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_184_, v_tokenNew_185_, v_kindNew_186_, v_a_189_, v_a_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object* v_stx_193_, lean_object* v_tokenNew_194_, lean_object* v_kindNew_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(v_stx_193_, v_tokenNew_194_, v_kindNew_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(lean_object* v_msgData_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_env_209_; lean_object* v___x_210_; lean_object* v_toCold_211_; lean_object* v_mctx_212_; lean_object* v_lctx_213_; lean_object* v_options_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_208_ = lean_st_ref_get(v___y_206_);
v_env_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_env_209_);
lean_dec(v___x_208_);
v___x_210_ = lean_st_ref_get(v___y_204_);
v_toCold_211_ = lean_ctor_get(v___y_205_, 0);
v_mctx_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_mctx_212_);
lean_dec(v___x_210_);
v_lctx_213_ = lean_ctor_get(v___y_203_, 2);
v_options_214_ = lean_ctor_get(v_toCold_211_, 2);
lean_inc_ref(v_options_214_);
lean_inc_ref(v_lctx_213_);
v___x_215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_215_, 0, v_env_209_);
lean_ctor_set(v___x_215_, 1, v_mctx_212_);
lean_ctor_set(v___x_215_, 2, v_lctx_213_);
lean_ctor_set(v___x_215_, 3, v_options_214_);
v___x_216_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_msgData_202_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0___boxed(lean_object* v_msgData_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msgData_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_ref_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_ref_231_ = lean_ctor_get(v___y_228_, 2);
v___x_232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_inc(v_ref_231_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_ref_231_);
lean_ctor_set(v___x_237_, 1, v_a_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg___boxed(lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v_msg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__2));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object* v_stx_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__0));
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__1));
v___x_270_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_258_, v___x_268_, v___x_269_, v_a_265_, v_a_266_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref_known(v___x_270_, 1);
v___x_271_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpArith___closed__3, &l_Lean_Elab_Tactic_evalSimpArith___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3);
v___x_272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_271_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
return v___x_272_;
}
else
{
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object* v_stx_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Tactic_evalSimpArith(v_stx_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(lean_object* v_00_u03b1_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v_msg_285_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___boxed(lean_object* v_00_u03b1_296_, lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(v_00_u03b1_296_, v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1(){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_322_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1));
v___x_324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4));
v___x_325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArith___boxed), 10, 0);
v___x_326_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_322_, v___x_323_, v___x_324_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___boxed(lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
return v_res_328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object* v_stx_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0));
v___x_346_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2));
v___x_347_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_339_, v___x_345_, v___x_346_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec_ref_known(v___x_347_, 1);
v___x_348_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4, &l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4);
v___x_349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_348_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_349_;
}
else
{
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object* v_stx_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(v_stx_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object* v_stx_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(v_stx_357_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object* v_stx_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Elab_Tactic_evalSimpArithBang(v_stx_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1(){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_392_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1));
v___x_394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3));
v___x_395_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArithBang___boxed), 10, 0);
v___x_396_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_392_, v___x_393_, v___x_394_, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___boxed(lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
return v_res_398_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object* v_stx_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0));
v___x_416_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2));
v___x_417_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_409_, v___x_415_, v___x_416_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref_known(v___x_417_, 1);
v___x_418_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4, &l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4);
v___x_419_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_418_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
return v___x_419_;
}
else
{
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object* v_stx_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(v_stx_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object* v_stx_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(v_stx_427_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object* v_stx_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Elab_Tactic_evalSimpAllArith(v_stx_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1));
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3));
v___x_465_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArith___boxed), 10, 0);
v___x_466_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_462_, v___x_463_, v___x_464_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___boxed(lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
return v_res_468_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object* v_stx_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0));
v___x_486_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2));
v___x_487_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_479_, v___x_485_, v___x_486_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref_known(v___x_487_, 1);
v___x_488_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4, &l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4);
v___x_489_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_488_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_489_;
}
else
{
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object* v_stx_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(v_stx_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object* v_stx_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(v_stx_497_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object* v_stx_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_Tactic_evalSimpAllArithBang(v_stx_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1(){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1));
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3));
v___x_535_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed), 10, 0);
v___x_536_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_532_, v___x_533_, v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___boxed(lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
return v_res_538_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_SimpArith(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_SimpArith(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_Tactic_SimpArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_SimpArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_SimpArith(builtin);
}
#ifdef __cplusplus
}
#endif
