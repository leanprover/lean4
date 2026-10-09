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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
v_kind_9_ = lean_ctor_get(v_optConfig_7_, 1);
v_args_10_ = lean_ctor_get(v_optConfig_7_, 2);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_array_get_size(v_args_10_);
v___x_13_ = lean_nat_dec_lt(v___x_11_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec(v_item_5_);
v___x_14_ = l_Lean_Syntax_setArg(v_stx_4_, v___x_6_, v_optConfig_7_);
return v___x_14_;
}
else
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_33_; 
lean_inc_ref(v_args_10_);
lean_inc(v_kind_9_);
lean_inc(v_info_8_);
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
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(lean_object* v_stx_59_, lean_object* v_a_60_){
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
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_59_ = stack[0].m_obj;
lean_object* v_a_60_ = stack[1].m_obj;
lean_object* v_res_77_;
v_res_77_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_59_, v_a_60_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___boxed(lean_object* v_stx_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_78_, v_a_79_);
lean_dec_ref(v_a_79_);
return v_res_81_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object* v_stx_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_82_, v_a_83_);
return v___x_86_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_82_ = stack[0].m_obj;
lean_object* v_a_83_ = stack[1].m_obj;
lean_object* v_a_84_ = stack[2].m_obj;
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(v_stx_82_, v_a_83_, v_a_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object* v_stx_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(v_stx_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_92_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(lean_object* v_stx_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_ref_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_ref_101_ = lean_ctor_get(v_a_99_, 2);
v___x_102_ = 0;
v___x_103_ = l_Lean_SourceInfo_fromRef(v_ref_101_, v___x_102_);
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4));
v___x_105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6));
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7));
lean_inc_n(v___x_103_, 3);
v___x_107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_103_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1, &l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1);
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2));
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_111_, 0, v___x_103_);
lean_ctor_set(v___x_111_, 1, v___x_108_);
lean_ctor_set(v___x_111_, 2, v___x_109_);
lean_ctor_set(v___x_111_, 3, v___x_110_);
v___x_112_ = l_Lean_Syntax_node2(v___x_103_, v___x_105_, v___x_107_, v___x_111_);
v___x_113_ = l_Lean_Syntax_node1(v___x_103_, v___x_104_, v___x_112_);
v___x_114_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(v_stx_98_, v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_98_ = stack[0].m_obj;
lean_object* v_a_99_ = stack[1].m_obj;
lean_object* v_res_116_;
v_res_116_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_98_, v_a_99_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___boxed(lean_object* v_stx_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_117_, v_a_118_);
lean_dec_ref(v_a_118_);
return v_res_120_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object* v_stx_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_121_, v_a_122_);
return v___x_125_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_121_ = stack[0].m_obj;
lean_object* v_a_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_res_126_;
v_res_126_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(v_stx_121_, v_a_122_, v_a_123_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object* v_stx_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(v_stx_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object* v_stx_132_, lean_object* v_str_133_, lean_object* v_kind_134_){
_start:
{
lean_object* v_stx_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_stx_135_ = l_Lean_Syntax_setKind(v_stx_132_, v_kind_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Lean_mkAtom(v_str_133_);
v___x_138_ = l_Lean_Syntax_setArg(v_stx_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(lean_object* v_stx_143_, lean_object* v_tokenNew_144_, lean_object* v_kindNew_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_stx_x27_149_; lean_object* v_stx_x27_150_; lean_object* v___x_151_; lean_object* v_a_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_180_; 
lean_inc(v_stx_143_);
v_stx_x27_149_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(v_stx_143_, v_tokenNew_144_, v_kindNew_145_);
v_stx_x27_150_ = l_Lean_Syntax_unsetTrailing(v_stx_x27_149_);
lean_inc(v_stx_x27_150_);
v___x_151_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_stx_x27_150_, v_a_146_);
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref(v___x_151_);
v___x_153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1));
v___x_154_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(v_stx_x27_150_, v_a_146_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(v_a_155_, v_a_146_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_180_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_180_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_180_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_ref_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v_ref_161_ = lean_ctor_get(v_a_146_, 2);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = l_Lean_Syntax_getArg(v_stx_143_, v___x_162_);
lean_dec(v_stx_143_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_153_);
lean_ctor_set(v___x_164_, 1, v_a_152_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_ctor_set(v___x_166_, 3, v___x_165_);
lean_ctor_set(v___x_166_, 4, v___x_165_);
lean_ctor_set(v___x_166_, 5, v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_153_);
lean_ctor_set(v___x_167_, 1, v_a_157_);
v___x_168_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_165_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
lean_ctor_set(v___x_168_, 3, v___x_165_);
lean_ctor_set(v___x_168_, 4, v___x_165_);
lean_ctor_set(v___x_168_, 5, v___x_165_);
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_array_push(v___x_170_, v___x_166_);
v___x_172_ = lean_array_push(v___x_171_, v___x_168_);
lean_inc(v_ref_161_);
if (v_isShared_160_ == 0)
{
lean_ctor_set_tag(v___x_159_, 1);
lean_ctor_set(v___x_159_, 0, v_ref_161_);
v___x_174_ = v___x_159_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_ref_161_);
v___x_174_ = v_reuseFailAlloc_179_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2));
v___x_176_ = 4;
v___x_177_ = l_Lean_MessageData_nil;
v___x_178_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v___x_163_, v___x_172_, v___x_174_, v___x_175_, v___x_165_, v___x_176_, v___x_177_, v_a_146_, v_a_147_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_143_ = stack[0].m_obj;
lean_object* v_tokenNew_144_ = stack[1].m_obj;
lean_object* v_kindNew_145_ = stack[2].m_obj;
lean_object* v_a_146_ = stack[3].m_obj;
lean_object* v_a_147_ = stack[4].m_obj;
lean_object* v_res_181_;
v_res_181_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_143_, v_tokenNew_144_, v_kindNew_145_, v_a_146_, v_a_147_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___boxed(lean_object* v_stx_182_, lean_object* v_tokenNew_183_, lean_object* v_kindNew_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_182_, v_tokenNew_183_, v_kindNew_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_188_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object* v_stx_189_, lean_object* v_tokenNew_190_, lean_object* v_kindNew_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_189_, v_tokenNew_190_, v_kindNew_191_, v_a_194_, v_a_195_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_189_ = stack[0].m_obj;
lean_object* v_tokenNew_190_ = stack[1].m_obj;
lean_object* v_kindNew_191_ = stack[2].m_obj;
lean_object* v_a_192_ = stack[3].m_obj;
lean_object* v_a_193_ = stack[4].m_obj;
lean_object* v_a_194_ = stack[5].m_obj;
lean_object* v_a_195_ = stack[6].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(v_stx_189_, v_tokenNew_190_, v_kindNew_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object* v_stx_199_, lean_object* v_tokenNew_200_, lean_object* v_kindNew_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(v_stx_199_, v_tokenNew_200_, v_kindNew_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
return v_res_207_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(lean_object* v_msgData_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; lean_object* v_env_215_; uint8_t v___x_216_; lean_object* v_env_217_; lean_object* v___x_218_; lean_object* v_toCold_219_; lean_object* v_mctx_220_; lean_object* v_lctx_221_; lean_object* v_options_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_214_ = lean_st_ref_get(v___y_212_);
v_env_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_env_215_);
lean_dec(v___x_214_);
v___x_216_ = 0;
v_env_217_ = l_Lean_Environment_setRecordingDeps(v_env_215_, v___x_216_);
v___x_218_ = lean_st_ref_get(v___y_210_);
v_toCold_219_ = lean_ctor_get(v___y_211_, 0);
v_mctx_220_ = lean_ctor_get(v___x_218_, 0);
lean_inc_ref(v_mctx_220_);
lean_dec(v___x_218_);
v_lctx_221_ = lean_ctor_get(v___y_209_, 2);
v_options_222_ = lean_ctor_get(v_toCold_219_, 2);
lean_inc_ref(v_options_222_);
lean_inc_ref(v_lctx_221_);
v___x_223_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_223_, 0, v_env_217_);
lean_ctor_set(v___x_223_, 1, v_mctx_220_);
lean_ctor_set(v___x_223_, 2, v_lctx_221_);
lean_ctor_set(v___x_223_, 3, v_options_222_);
v___x_224_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_msgData_208_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_208_ = stack[0].m_obj;
lean_object* v___y_209_ = stack[1].m_obj;
lean_object* v___y_210_ = stack[2].m_obj;
lean_object* v___y_211_ = stack[3].m_obj;
lean_object* v___y_212_ = stack[4].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msgData_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0___boxed(lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msgData_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_233_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(lean_object* v_msg_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_ref_240_; lean_object* v___x_241_; lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_250_; 
v_ref_240_ = lean_ctor_get(v___y_237_, 2);
v___x_241_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msg_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_250_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_inc(v_ref_240_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_ref_240_);
lean_ctor_set(v___x_246_, 1, v_a_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 1);
lean_ctor_set(v___x_244_, 0, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_234_ = stack[0].m_obj;
lean_object* v___y_235_ = stack[1].m_obj;
lean_object* v___y_236_ = stack[2].m_obj;
lean_object* v___y_237_ = stack[3].m_obj;
lean_object* v___y_238_ = stack[4].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v_msg_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg___boxed(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__2));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object* v_stx_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__0));
v___x_279_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArith___closed__1));
v___x_280_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_268_, v___x_278_, v___x_279_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_281_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpArith___closed__3, &l_Lean_Elab_Tactic_evalSimpArith___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3);
v___x_282_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_281_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_282_;
}
else
{
return v___x_280_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpArith_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_268_ = stack[0].m_obj;
lean_object* v_a_269_ = stack[1].m_obj;
lean_object* v_a_270_ = stack[2].m_obj;
lean_object* v_a_271_ = stack[3].m_obj;
lean_object* v_a_272_ = stack[4].m_obj;
lean_object* v_a_273_ = stack[5].m_obj;
lean_object* v_a_274_ = stack[6].m_obj;
lean_object* v_a_275_ = stack[7].m_obj;
lean_object* v_a_276_ = stack[8].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Lean_Elab_Tactic_evalSimpArith(v_stx_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object* v_stx_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Elab_Tactic_evalSimpArith(v_stx_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
return v_res_294_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(lean_object* v_00_u03b1_295_, lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v_msg_296_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v___x_306_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_296_ = stack[1].m_obj;
lean_object* v___y_297_ = stack[2].m_obj;
lean_object* v___y_298_ = stack[3].m_obj;
lean_object* v___y_299_ = stack[4].m_obj;
lean_object* v___y_300_ = stack[5].m_obj;
lean_object* v___y_301_ = stack[6].m_obj;
lean_object* v___y_302_ = stack[7].m_obj;
lean_object* v___y_303_ = stack[8].m_obj;
lean_object* v___y_304_ = stack[9].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(lean_box(0), v_msg_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___boxed(lean_object* v_00_u03b1_308_, lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(v_00_u03b1_308_, v_msg_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_319_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1(){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_334_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1));
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4));
v___x_337_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArith___boxed), 10, 0);
v___x_338_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_334_, v___x_335_, v___x_336_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_339_;
v_res_339_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___boxed(lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
return v_res_341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object* v_stx_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0));
v___x_359_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2));
v___x_360_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_352_, v___x_358_, v___x_359_, v_a_355_, v_a_356_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref_known(v___x_360_, 1);
v___x_361_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4, &l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4);
v___x_362_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_361_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_362_;
}
else
{
return v___x_360_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpArithBang___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_352_ = stack[0].m_obj;
lean_object* v_a_353_ = stack[1].m_obj;
lean_object* v_a_354_ = stack[2].m_obj;
lean_object* v_a_355_ = stack[3].m_obj;
lean_object* v_a_356_ = stack[4].m_obj;
lean_object* v_res_363_;
v_res_363_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(v_stx_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object* v_stx_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(v_stx_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object* v_stx_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(v_stx_371_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpArithBang_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_371_ = stack[0].m_obj;
lean_object* v_a_372_ = stack[1].m_obj;
lean_object* v_a_373_ = stack[2].m_obj;
lean_object* v_a_374_ = stack[3].m_obj;
lean_object* v_a_375_ = stack[4].m_obj;
lean_object* v_a_376_ = stack[5].m_obj;
lean_object* v_a_377_ = stack[6].m_obj;
lean_object* v_a_378_ = stack[7].m_obj;
lean_object* v_a_379_ = stack[8].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Elab_Tactic_evalSimpArithBang(v_stx_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object* v_stx_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_Tactic_evalSimpArithBang(v_stx_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_393_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1(){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1));
v___x_409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3));
v___x_410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArithBang___boxed), 10, 0);
v___x_411_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_407_, v___x_408_, v___x_409_, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_412_;
v_res_412_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___boxed(lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
return v_res_414_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object* v_stx_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0));
v___x_432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2));
v___x_433_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_425_, v___x_431_, v___x_432_, v_a_428_, v_a_429_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref_known(v___x_433_, 1);
v___x_434_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4, &l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4);
v___x_435_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_434_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
return v___x_435_;
}
else
{
return v___x_433_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpAllArith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_425_ = stack[0].m_obj;
lean_object* v_a_426_ = stack[1].m_obj;
lean_object* v_a_427_ = stack[2].m_obj;
lean_object* v_a_428_ = stack[3].m_obj;
lean_object* v_a_429_ = stack[4].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(v_stx_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object* v_stx_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(v_stx_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_443_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object* v_stx_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(v_stx_444_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpAllArith_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_444_ = stack[0].m_obj;
lean_object* v_a_445_ = stack[1].m_obj;
lean_object* v_a_446_ = stack[2].m_obj;
lean_object* v_a_447_ = stack[3].m_obj;
lean_object* v_a_448_ = stack[4].m_obj;
lean_object* v_a_449_ = stack[5].m_obj;
lean_object* v_a_450_ = stack[6].m_obj;
lean_object* v_a_451_ = stack[7].m_obj;
lean_object* v_a_452_ = stack[8].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_Elab_Tactic_evalSimpAllArith(v_stx_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object* v_stx_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Elab_Tactic_evalSimpAllArith(v_stx_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_466_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1(){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_480_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1));
v___x_482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3));
v___x_483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArith___boxed), 10, 0);
v___x_484_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_480_, v___x_481_, v___x_482_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_485_;
v_res_485_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___boxed(lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
return v_res_487_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object* v_stx_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0));
v___x_505_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2));
v___x_506_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(v_stx_498_, v___x_504_, v___x_505_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref_known(v___x_506_, 1);
v___x_507_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4, &l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4);
v___x_508_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(v___x_507_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v___x_508_;
}
else
{
return v___x_506_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_498_ = stack[0].m_obj;
lean_object* v_a_499_ = stack[1].m_obj;
lean_object* v_a_500_ = stack[2].m_obj;
lean_object* v_a_501_ = stack[3].m_obj;
lean_object* v_a_502_ = stack[4].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(v_stx_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object* v_stx_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(v_stx_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_516_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object* v_stx_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(v_stx_517_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_527_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpAllArithBang_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_517_ = stack[0].m_obj;
lean_object* v_a_518_ = stack[1].m_obj;
lean_object* v_a_519_ = stack[2].m_obj;
lean_object* v_a_520_ = stack[3].m_obj;
lean_object* v_a_521_ = stack[4].m_obj;
lean_object* v_a_522_ = stack[5].m_obj;
lean_object* v_a_523_ = stack[6].m_obj;
lean_object* v_a_524_ = stack[7].m_obj;
lean_object* v_a_525_ = stack[8].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lean_Elab_Tactic_evalSimpAllArithBang(v_stx_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object* v_stx_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_Tactic_evalSimpAllArithBang(v_stx_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_539_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1(){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1));
v___x_555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3));
v___x_556_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed), 10, 0);
v___x_557_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_553_, v___x_554_, v___x_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_558_;
v_res_558_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___boxed(lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
return v_res_560_;
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
