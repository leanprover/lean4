// Lean compiler output
// Module: Lean.Elab.Notation
// Imports: public import Lean.Elab.Syntax public import Lean.Elab.AuxDef public import Lean.Elab.BuiltinNotation
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inherit_doc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(83, 8, 69, 42, 53, 230, 51, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_addInheritDocDefault___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__0 = (const lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__1 = (const lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_addInheritDocDefault___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__2 = (const lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__2_value;
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "identPrec"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value),LEAN_SCALAR_PTR_LITERAL(251, 25, 252, 182, 120, 175, 78, 126)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unicodeAtom"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value),LEAN_SCALAR_PTR_LITERAL(29, 147, 94, 13, 45, 35, 101, 109)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_removeParentheses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__0 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__1 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_removeParentheses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__2 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__3 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_removeParentheses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__4 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__5 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__0_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 107, 218, 203, 20, 35, 251, 156)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__3_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__4;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__6 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__7 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__8 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__9 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__9_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__10 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__11 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__11_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__12 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__13 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "app_unexpander"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__14 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__14_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__14_value),LEAN_SCALAR_PTR_LITERAL(173, 94, 177, 152, 198, 163, 81, 20)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__16 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__17 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unexpand"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__18 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__18_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__19;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__18_value),LEAN_SCALAR_PTR_LITERAL(42, 154, 37, 229, 99, 64, 199, 76)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__20 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.PrettyPrinter.Unexpander"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__21 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__21_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__22;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__23 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Unexpander"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__24 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__23_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__24_value),LEAN_SCALAR_PTR_LITERAL(127, 37, 73, 100, 13, 145, 76, 255)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__25 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__26 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__26_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__27 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__27_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__28 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__29 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__29_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__30 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__31 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__31_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__32 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__33 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__34 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__34_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__35 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__36 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__37 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__37_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__38 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "withRef"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__39 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__39_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__40;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__39_value),LEAN_SCALAR_PTR_LITERAL(193, 74, 233, 14, 30, 198, 157, 185)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__41 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__39_value),LEAN_SCALAR_PTR_LITERAL(128, 176, 237, 189, 54, 129, 101, 238)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__42 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__43 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__43_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__44 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__45 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "throw"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__46 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__46_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__47;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__46_value),LEAN_SCALAR_PTR_LITERAL(60, 81, 80, 209, 187, 239, 255, 113)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__48 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__48_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadExcept"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__49 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__49_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__49_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__46_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 61, 69, 62, 207, 229, 53)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__50 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__50_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__51 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__51_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__52 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__53 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__53_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__54 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__54_value;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__55;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__56 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__57 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__58 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__59 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__60 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__61 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__62 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__62_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__63 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__63_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__64 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__61_value),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__64_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__65 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__59_value),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__65_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__66 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__57_value),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__66_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__67 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__67_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__68;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__69;
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2_value;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1_value;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0;
static lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "macro_rules"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__2_value),LEAN_SCALAR_PTR_LITERAL(125, 80, 75, 5, 165, 87, 197, 1)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckedQuot"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__8_value;
static lean_object* l_Lean_Elab_Command_elabNotation___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__13_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__15_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed__const__1;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabNotation"};
static const lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 81, 117, 114, 113, 220, 215, 248)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
x_8 = l_Lean_TSyntax_getId(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(x_2);
x_4 = l_Lean_Syntax_isOfKind(x_2, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_7, x_8, x_6);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_13, x_14, x_12);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
else
{
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
return x_2;
}
else
{
if (x_19 == 0)
{
return x_2;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_18);
x_22 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(x_2, x_1, x_20, x_21);
if (x_22 == 0)
{
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
x_24 = lean_box(0);
x_25 = l_Lean_Syntax_mkAntiquotNode(x_23, x_2, x_17, x_24, x_4);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
lean_inc(x_8);
x_17 = l_Lean_Syntax_isOfKind(x_8, x_7);
if (x_17 == 0)
{
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Syntax_getArg(x_8, x_9);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(x_18);
x_20 = l_Lean_Syntax_isOfKind(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_18);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Syntax_getArg(x_18, x_9);
lean_dec(x_18);
x_22 = l_Lean_Syntax_matchesNull(x_21, x_9);
if (x_22 == 0)
{
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_8, x_23);
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_24);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
x_28 = l_Lean_Syntax_getArg(x_24, x_9);
lean_inc(x_28);
x_29 = l_Lean_Syntax_isOfKind(x_28, x_27);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_24);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Syntax_getArg(x_24, x_23);
lean_dec(x_24);
x_31 = l_Lean_Syntax_matchesNull(x_30, x_9);
if (x_31 == 0)
{
lean_dec(x_28);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_TSyntax_getId(x_28);
x_33 = lean_erase_macro_scopes(x_32);
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_dec(x_28);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
x_36 = lean_box(0);
x_37 = l_Lean_SourceInfo_fromRef(x_36, x_1);
x_38 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_39 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
lean_inc(x_37);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_37);
x_41 = l_Lean_Syntax_node1(x_37, x_19, x_40);
lean_inc(x_2);
lean_inc(x_37);
x_42 = l_Lean_Syntax_node1(x_37, x_38, x_2);
lean_inc(x_37);
x_43 = l_Lean_Syntax_node2(x_37, x_25, x_28, x_42);
x_44 = l_Lean_Syntax_node2(x_37, x_7, x_41, x_43);
x_11 = x_44;
goto block_16;
}
}
}
}
}
}
}
block_16:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_14 = lean_array_uset(x_10, x_4, x_11);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(x_6, x_2, x_7, x_8, x_5);
return x_9;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_SourceInfo_fromRef(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_3 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1;
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
x_3 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0;
x_4 = l_Lean_Syntax_node1(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_6 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
lean_inc(x_7);
x_16 = l_Lean_Syntax_isOfKind(x_7, x_6);
if (x_16 == 0)
{
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Syntax_getArg(x_7, x_8);
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_17);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Syntax_getArg(x_17, x_8);
lean_dec(x_17);
x_21 = l_Lean_Syntax_matchesNull(x_20, x_8);
if (x_21 == 0)
{
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_7, x_22);
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(x_23);
x_25 = l_Lean_Syntax_isOfKind(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_23);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
x_27 = l_Lean_Syntax_getArg(x_23, x_8);
lean_inc(x_27);
x_28 = l_Lean_Syntax_isOfKind(x_27, x_26);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_23);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Syntax_getArg(x_23, x_22);
lean_dec(x_23);
x_30 = l_Lean_Syntax_matchesNull(x_29, x_8);
if (x_30 == 0)
{
lean_dec(x_27);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_Lean_TSyntax_getId(x_27);
x_32 = lean_erase_macro_scopes(x_31);
x_33 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
x_34 = lean_name_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec(x_27);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
x_35 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0;
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_37 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2;
lean_inc(x_1);
x_38 = l_Lean_Syntax_node1(x_35, x_36, x_1);
x_39 = l_Lean_Syntax_node2(x_35, x_24, x_27, x_38);
x_40 = l_Lean_Syntax_node2(x_35, x_6, x_37, x_39);
x_10 = x_40;
goto block_15;
}
}
}
}
}
}
}
block_15:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_9, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_8; 
lean_inc(x_3);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
x_11 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_12 = lean_array_size(x_11);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(x_5, x_1, x_12, x_13, x_11);
x_15 = l_Lean_Syntax_SepArray_ofElems(x_10, x_14);
lean_dec_ref(x_14);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_16 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
x_17 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(x_5, x_1, x_18, x_19, x_17);
x_21 = l_Lean_Syntax_SepArray_ofElems(x_16, x_20);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_24);
return x_2;
}
else
{
uint8_t x_27; 
lean_inc(x_3);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
x_30 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_31 = lean_array_size(x_30);
x_32 = 0;
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(x_24, x_31, x_32, x_30);
x_34 = l_Lean_Syntax_SepArray_ofElems(x_29, x_33);
lean_dec_ref(x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_35 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
x_36 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_37 = lean_array_size(x_36);
x_38 = 0;
x_39 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(x_24, x_37, x_38, x_36);
x_40 = l_Lean_Syntax_SepArray_ofElems(x_35, x_39);
lean_dec_ref(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
lean_inc(x_1);
x_41 = l_Lean_Syntax_isOfKind(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
lean_inc(x_1);
x_43 = l_Lean_Syntax_isOfKind(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_dec_ref(x_2);
x_44 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(x_1);
x_45 = l_Lean_Syntax_isOfKind(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
lean_dec_ref(x_2);
x_49 = l_Lean_SourceInfo_fromRef(x_48, x_41);
lean_dec(x_48);
x_50 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
x_51 = l_Lean_Syntax_node1(x_49, x_50, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Syntax_getArg(x_1, x_53);
x_55 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
x_56 = l_Lean_Syntax_isOfKind(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
lean_dec_ref(x_2);
x_57 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(x_1);
x_58 = l_Lean_Syntax_isOfKind(x_1, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_1);
x_59 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = l_Lean_Syntax_getArg(x_1, x_61);
x_63 = l_Lean_Syntax_isNone(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_inc(x_62);
x_64 = l_Lean_Syntax_matchesNull(x_62, x_61);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_62);
lean_dec_ref(x_2);
x_65 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(x_1);
x_66 = l_Lean_Syntax_isOfKind(x_1, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_1);
x_67 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = l_Lean_Syntax_getArg(x_62, x_53);
lean_dec(x_62);
x_70 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(x_69);
x_71 = l_Lean_Syntax_isOfKind(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_69);
lean_dec_ref(x_2);
x_72 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(x_1);
x_73 = l_Lean_Syntax_isOfKind(x_1, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_1);
x_74 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_76 = l_Lean_Syntax_getArg(x_69, x_61);
lean_dec(x_69);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_16 = x_77;
x_17 = x_2;
x_18 = x_3;
goto block_39;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_62);
lean_dec(x_1);
x_78 = lean_box(0);
x_16 = x_78;
x_17 = x_2;
x_18 = x_3;
goto block_39;
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Array_append___redArg(x_9, x_10);
lean_dec_ref(x_10);
lean_inc(x_7);
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_Syntax_node2(x_7, x_6, x_5, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
block_39:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 5);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
lean_dec(x_21);
x_24 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2));
x_25 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3;
x_26 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
x_27 = l_Lean_addMacroScope(x_19, x_26, x_20);
x_28 = lean_box(0);
lean_inc(x_23);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_31 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec_ref(x_16);
x_33 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
x_34 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_23);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_23);
x_36 = l_Lean_Syntax_node2(x_23, x_33, x_35, x_32);
x_37 = l_Array_mkArray1___redArg(x_36);
x_4 = x_18;
x_5 = x_29;
x_6 = x_24;
x_7 = x_23;
x_8 = x_30;
x_9 = x_31;
x_10 = x_37;
goto block_15;
}
else
{
lean_object* x_38; 
lean_dec(x_16);
x_38 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
x_4 = x_18;
x_5 = x_29;
x_6 = x_24;
x_7 = x_23;
x_8 = x_30;
x_9 = x_31;
x_10 = x_38;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
x_15 = lean_name_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
x_17 = lean_name_eq(x_11, x_16);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = l_Lean_Macro_throwUnsupported___redArg(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(4u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
x_3 = x_17;
goto block_10;
}
else
{
x_3 = x_15;
goto block_10;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
x_22 = l_Lean_Elab_Command_strLitToPattern___redArg(x_1, x_2);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_23 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = l_Lean_Syntax_mkAntiquotNode(x_23, x_25, x_24, x_26, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
return x_28;
}
block_10:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
lean_dec(x_1);
x_6 = l_Lean_Elab_Command_strLitToPattern___redArg(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l_Lean_Elab_Command_strLitToPattern___redArg(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNotationItemIntoPattern(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_getHeadInfo(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Lean_Syntax_getTailInfo(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 3);
x_14 = lean_ctor_get(x_9, 2);
lean_dec(x_14);
x_15 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 2);
x_18 = lean_ctor_get(x_15, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 0, x_4);
x_21 = l_Lean_Syntax_setHeadInfo(x_2, x_15);
lean_ctor_set(x_9, 2, x_17);
x_22 = l_Lean_Syntax_setTailInfo(x_21, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
lean_ctor_set(x_24, 3, x_8);
x_25 = l_Lean_Syntax_setHeadInfo(x_2, x_24);
lean_ctor_set(x_9, 2, x_23);
x_26 = l_Lean_Syntax_setTailInfo(x_25, x_9);
return x_26;
}
}
else
{
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_30 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc_ref(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 4, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
x_34 = l_Lean_Syntax_setHeadInfo(x_2, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_29);
x_36 = l_Lean_Syntax_setTailInfo(x_34, x_35);
return x_36;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_2;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_2;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_10, x_11, x_9, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_25 = lean_array_size(x_24);
x_26 = 0;
x_27 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_25, x_26, x_24, x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
lean_dec(x_22);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec_ref(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
x_40 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
lean_inc(x_39);
x_41 = l_Lean_Syntax_isOfKind(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_39);
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_array_size(x_45);
x_47 = 0;
x_48 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_46, x_47, x_45, x_2, x_3);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_1, 2, x_50);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_1, 2, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_1);
lean_dec(x_44);
lean_dec(x_43);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_61 = lean_array_size(x_60);
x_62 = 0;
x_63 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_61, x_62, x_60, x_2, x_3);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
lean_dec(x_58);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec_ref(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_39, x_74);
lean_dec(x_39);
x_76 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
lean_inc(x_75);
x_77 = l_Lean_Syntax_isOfKind(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_75);
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_1, 0);
x_80 = lean_ctor_get(x_1, 1);
x_81 = lean_ctor_get(x_1, 2);
x_82 = lean_array_size(x_81);
x_83 = 0;
x_84 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_82, x_83, x_81, x_2, x_3);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_1, 2, x_86);
lean_ctor_set(x_84, 0, x_1);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_1, 2, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_free_object(x_1);
lean_dec(x_80);
lean_dec(x_79);
x_90 = !lean_is_exclusive(x_84);
if (x_90 == 0)
{
return x_84;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_84, 0);
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_84);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
x_96 = lean_ctor_get(x_1, 2);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_97 = lean_array_size(x_96);
x_98 = 0;
x_99 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_97, x_98, x_96, x_2, x_3);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_103, 2, x_100);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_95);
lean_dec(x_94);
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec_ref(x_2);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_3);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = l_Lean_Syntax_getArg(x_1, x_74);
x_111 = l_Lean_TSyntax_getHygieneInfo(x_75);
lean_dec(x_75);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_inc_ref(x_2);
lean_inc(x_110);
x_113 = l_Lean_Elab_Term_expandCDot_x3f(x_110, x_112, x_2, x_3);
lean_dec_ref(x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
if (lean_obj_tag(x_114) == 0)
{
x_116 = x_110;
goto block_125;
}
else
{
lean_object* x_126; 
lean_dec(x_110);
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec_ref(x_114);
x_116 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_117; 
x_117 = l_Lean_Elab_Command_removeParentheses(x_116, x_2, x_115);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_119);
lean_dec(x_1);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_117);
x_123 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_121);
lean_dec(x_1);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_dec(x_1);
return x_117;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_110);
lean_dec_ref(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_113);
if (x_127 == 0)
{
return x_113;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_113, 0);
x_129 = lean_ctor_get(x_113, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_113);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc_ref(x_4);
x_9 = l_Lean_Elab_Command_removeParentheses(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_15;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_17; lean_object* x_18; uint8_t x_29; 
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 0);
lean_dec(x_31);
x_32 = lean_box(0);
x_33 = l_Lean_Syntax_isAntiquot(x_2);
if (x_33 == 0)
{
lean_object* x_34; 
lean_ctor_set(x_3, 0, x_32);
lean_inc_ref(x_3);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_3);
x_17 = x_34;
x_18 = x_3;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Syntax_getAntiquotTerm(x_2);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = l_Lean_NameSet_contains(x_30, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_NameSet_insert(x_30, x_36);
lean_ctor_set(x_3, 1, x_38);
lean_ctor_set(x_3, 0, x_32);
lean_inc_ref(x_3);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_17 = x_39;
x_18 = x_3;
goto block_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_2);
x_40 = lean_box(x_37);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_3, 0, x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_3);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_box(0);
x_45 = l_Lean_Syntax_isAntiquot(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_43);
lean_inc_ref(x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_17 = x_47;
x_18 = x_46;
goto block_28;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Lean_Syntax_getAntiquotTerm(x_2);
x_49 = l_Lean_Syntax_getId(x_48);
lean_dec(x_48);
x_50 = l_Lean_NameSet_contains(x_43, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Lean_NameSet_insert(x_43, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
lean_inc_ref(x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_17 = x_53;
x_18 = x_52;
goto block_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_2);
x_54 = lean_box(x_50);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_array_size(x_5);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(x_1, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
return x_15;
}
}
block_28:
{
if (lean_obj_tag(x_2) == 1)
{
lean_dec_ref(x_17);
if (x_1 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_2);
x_5 = x_19;
x_6 = x_18;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_2);
x_22 = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
x_23 = lean_name_eq(x_20, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
x_5 = x_21;
x_6 = x_18;
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_21, x_25);
lean_dec_ref(x_21);
x_2 = x_26;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_2);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_array_uget(x_3, x_5);
lean_inc(x_9);
x_12 = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_11, x_9, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_box(0);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_15);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_array_uget(x_3, x_5);
lean_inc(x_19);
x_21 = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_20, x_19, x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_19);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_5 = x_28;
x_6 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_5, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_array_uget(x_1, x_3);
x_9 = l_Lean_Syntax_topDown(x_8, x_5);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(0);
lean_ctor_set(x_4, 0, x_12);
lean_inc_ref(x_4);
x_30 = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_10, x_11, x_4, x_4);
lean_dec_ref(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_13 = x_31;
goto block_29;
block_29:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_12);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_21;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_inc_ref(x_14);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 0);
lean_dec(x_26);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_array_uget(x_1, x_3);
x_34 = l_Lean_Syntax_topDown(x_33, x_5);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_32);
lean_inc_ref(x_50);
x_51 = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_35, x_36, x_50, x_50);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_38 = x_52;
goto block_49;
block_49:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_40);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_3 = x_44;
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_39);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_47 = x_38;
} else {
 lean_dec_ref(x_38);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0;
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(x_1, x_3, x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__14));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__18));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__21));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__39));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__46));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_604; uint8_t x_605; 
x_604 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(x_3);
x_605 = l_Lean_Syntax_isOfKind(x_3, x_604);
if (x_605 == 0)
{
lean_object* x_606; uint8_t x_607; 
x_606 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(x_3);
x_607 = l_Lean_Syntax_isOfKind(x_3, x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_608 = lean_box(0);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_5);
return x_609;
}
else
{
lean_object* x_610; 
x_610 = l_Lean_Elab_Command_mkUnexpander___closed__69;
x_10 = x_3;
x_11 = x_610;
x_12 = x_4;
x_13 = x_5;
goto block_603;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; uint8_t x_614; 
x_611 = lean_unsigned_to_nat(0u);
x_612 = l_Lean_Syntax_getArg(x_3, x_611);
x_613 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(x_612);
x_614 = l_Lean_Syntax_isOfKind(x_612, x_613);
if (x_614 == 0)
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_612);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_615 = lean_box(0);
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_5);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_unsigned_to_nat(1u);
x_618 = l_Lean_Syntax_getArg(x_3, x_617);
lean_dec(x_3);
x_619 = l_Lean_Syntax_getArgs(x_618);
lean_dec(x_618);
x_10 = x_612;
x_11 = x_619;
x_12 = x_4;
x_13 = x_5;
goto block_603;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_603:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_TSyntax_getId(x_10);
lean_dec(x_10);
lean_inc_ref(x_12);
x_15 = l_Lean_Macro_resolveGlobalName(x_14, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec_ref(x_15);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_dec(x_25);
x_26 = lean_array_size(x_11);
x_27 = 0;
lean_inc_ref(x_12);
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_26, x_27, x_11, x_12, x_22);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 5);
lean_inc(x_34);
lean_dec_ref(x_12);
x_35 = l_Lean_SourceInfo_fromRef(x_34, x_31);
lean_dec(x_34);
x_36 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
x_37 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
x_38 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(x_35);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_38);
lean_ctor_set(x_17, 0, x_35);
x_39 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_40 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
lean_inc(x_35);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_43 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc(x_33);
lean_inc(x_32);
x_44 = l_Lean_addMacroScope(x_32, x_43, x_33);
x_45 = lean_box(0);
lean_inc(x_35);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
x_47 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
x_48 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_35);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_35);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_36);
lean_inc_ref(x_49);
lean_inc(x_35);
x_51 = l_Lean_Syntax_node2(x_35, x_47, x_49, x_50);
lean_inc_ref(x_46);
lean_inc_ref(x_41);
lean_inc(x_35);
x_52 = l_Lean_Syntax_node4(x_35, x_37, x_17, x_41, x_46, x_51);
x_53 = l_Lean_Syntax_mkApp(x_52, x_30);
lean_inc(x_1);
x_54 = l_Lean_Parser_Command_visibility_ofAttrKind(x_1);
x_55 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
x_56 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
x_57 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
x_58 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(x_35);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_35);
lean_ctor_set(x_59, 1, x_58);
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
x_62 = l_Lean_Elab_Command_mkUnexpander___closed__15;
x_63 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
lean_inc(x_33);
lean_inc(x_32);
x_64 = l_Lean_addMacroScope(x_32, x_63, x_33);
lean_inc(x_35);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_35);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_45);
x_66 = lean_mk_syntax_ident(x_24);
lean_inc(x_66);
lean_inc(x_35);
x_67 = l_Lean_Syntax_node1(x_35, x_39, x_66);
lean_inc(x_35);
x_68 = l_Lean_Syntax_node2(x_35, x_61, x_65, x_67);
lean_inc(x_35);
x_69 = l_Lean_Syntax_node2(x_35, x_60, x_1, x_68);
lean_inc(x_35);
x_70 = l_Lean_Syntax_node1(x_35, x_39, x_69);
x_71 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(x_35);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_35);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_35);
x_73 = l_Lean_Syntax_node3(x_35, x_57, x_59, x_70, x_72);
lean_inc(x_35);
x_74 = l_Lean_Syntax_node1(x_35, x_39, x_73);
lean_inc(x_35);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_35);
lean_ctor_set(x_75, 1, x_55);
x_76 = l_Lean_Elab_Command_mkUnexpander___closed__19;
x_77 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
lean_inc(x_33);
lean_inc(x_32);
x_78 = l_Lean_addMacroScope(x_32, x_77, x_33);
lean_inc(x_35);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_35);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_45);
lean_inc(x_35);
x_80 = l_Lean_Syntax_node2(x_35, x_39, x_79, x_66);
x_81 = l_Lean_Elab_Command_mkUnexpander___closed__22;
x_82 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
lean_inc(x_33);
lean_inc(x_32);
x_83 = l_Lean_addMacroScope(x_32, x_82, x_33);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_18);
lean_ctor_set(x_16, 1, x_45);
lean_ctor_set(x_16, 0, x_84);
lean_inc(x_35);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_16);
x_86 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(x_35);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_35);
lean_ctor_set(x_87, 1, x_86);
x_88 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
x_89 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
lean_inc(x_35);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_35);
lean_ctor_set(x_90, 1, x_88);
x_91 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
x_92 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
x_93 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(x_35);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_35);
lean_ctor_set(x_94, 1, x_93);
x_95 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
x_96 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(x_35);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_35);
lean_ctor_set(x_97, 1, x_96);
x_98 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(x_35);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_35);
lean_ctor_set(x_99, 1, x_98);
lean_inc_ref(x_99);
lean_inc_ref(x_97);
lean_inc(x_35);
x_100 = l_Lean_Syntax_node3(x_35, x_95, x_97, x_53, x_99);
lean_inc(x_35);
x_101 = l_Lean_Syntax_node1(x_35, x_39, x_100);
lean_inc(x_35);
x_102 = l_Lean_Syntax_node1(x_35, x_39, x_101);
x_103 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(x_35);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_35);
lean_ctor_set(x_104, 1, x_103);
x_105 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
x_106 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_107 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc(x_33);
lean_inc(x_32);
x_108 = l_Lean_addMacroScope(x_32, x_107, x_33);
x_109 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_18);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_45);
lean_inc(x_35);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_35);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set(x_112, 3, x_111);
lean_inc_ref(x_99);
lean_inc(x_35);
x_113 = l_Lean_Syntax_node3(x_35, x_95, x_97, x_2, x_99);
lean_inc(x_35);
x_114 = l_Lean_Syntax_node2(x_35, x_39, x_46, x_113);
lean_inc(x_35);
x_115 = l_Lean_Syntax_node2(x_35, x_105, x_112, x_114);
lean_inc_ref(x_104);
lean_inc_ref(x_94);
lean_inc(x_35);
x_116 = l_Lean_Syntax_node4(x_35, x_92, x_94, x_102, x_104, x_115);
x_117 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
x_118 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
lean_inc(x_35);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_35);
x_120 = l_Lean_Syntax_node1(x_35, x_117, x_119);
lean_inc(x_35);
x_121 = l_Lean_Syntax_node1(x_35, x_39, x_120);
lean_inc(x_35);
x_122 = l_Lean_Syntax_node1(x_35, x_39, x_121);
x_123 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_124 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
lean_inc(x_33);
lean_inc(x_32);
x_125 = l_Lean_addMacroScope(x_32, x_124, x_33);
x_126 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_18);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_45);
lean_inc(x_35);
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_35);
lean_ctor_set(x_129, 1, x_123);
lean_ctor_set(x_129, 2, x_125);
lean_ctor_set(x_129, 3, x_128);
x_130 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
x_131 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
x_132 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(x_35);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_35);
lean_ctor_set(x_133, 1, x_132);
x_134 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
x_135 = l_Lean_Elab_Command_mkUnexpander___closed__55;
x_136 = lean_box(0);
x_137 = l_Lean_addMacroScope(x_32, x_136, x_33);
x_138 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
lean_inc(x_35);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_35);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_35);
x_140 = l_Lean_Syntax_node1(x_35, x_134, x_139);
lean_inc(x_35);
x_141 = l_Lean_Syntax_node2(x_35, x_131, x_133, x_140);
lean_inc_ref(x_41);
lean_inc(x_35);
x_142 = l_Lean_Syntax_node3(x_35, x_130, x_141, x_41, x_99);
lean_inc(x_35);
x_143 = l_Lean_Syntax_node1(x_35, x_39, x_142);
lean_inc(x_35);
x_144 = l_Lean_Syntax_node2(x_35, x_105, x_129, x_143);
lean_inc(x_35);
x_145 = l_Lean_Syntax_node4(x_35, x_92, x_94, x_122, x_104, x_144);
lean_inc(x_35);
x_146 = l_Lean_Syntax_node2(x_35, x_39, x_116, x_145);
lean_inc(x_35);
x_147 = l_Lean_Syntax_node1(x_35, x_91, x_146);
lean_inc(x_35);
x_148 = l_Lean_Syntax_node2(x_35, x_89, x_90, x_147);
x_149 = l_Lean_Elab_Command_mkUnexpander___closed__68;
x_150 = lean_array_push(x_149, x_41);
x_151 = lean_array_push(x_150, x_74);
x_152 = lean_array_push(x_151, x_54);
x_153 = lean_array_push(x_152, x_75);
x_154 = lean_array_push(x_153, x_80);
x_155 = lean_array_push(x_154, x_49);
x_156 = lean_array_push(x_155, x_85);
x_157 = lean_array_push(x_156, x_87);
x_158 = lean_array_push(x_157, x_148);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_35);
lean_ctor_set(x_159, 1, x_56);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_28, 0, x_160);
return x_28;
}
else
{
lean_object* x_161; 
lean_dec(x_30);
lean_free_object(x_17);
lean_dec(x_24);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_box(0);
lean_ctor_set(x_28, 0, x_161);
return x_28;
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_28, 0);
x_163 = lean_ctor_get(x_28, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_28);
x_164 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_165 = lean_ctor_get(x_12, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_12, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_12, 5);
lean_inc(x_167);
lean_dec_ref(x_12);
x_168 = l_Lean_SourceInfo_fromRef(x_167, x_164);
lean_dec(x_167);
x_169 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
x_170 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
x_171 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(x_168);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_171);
lean_ctor_set(x_17, 0, x_168);
x_172 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_173 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
lean_inc(x_168);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_173);
x_175 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_176 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc(x_166);
lean_inc(x_165);
x_177 = l_Lean_addMacroScope(x_165, x_176, x_166);
x_178 = lean_box(0);
lean_inc(x_168);
x_179 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_175);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
x_180 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
x_181 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_168);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_168);
lean_ctor_set(x_182, 1, x_181);
lean_inc(x_168);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_168);
lean_ctor_set(x_183, 1, x_169);
lean_inc_ref(x_182);
lean_inc(x_168);
x_184 = l_Lean_Syntax_node2(x_168, x_180, x_182, x_183);
lean_inc_ref(x_179);
lean_inc_ref(x_174);
lean_inc(x_168);
x_185 = l_Lean_Syntax_node4(x_168, x_170, x_17, x_174, x_179, x_184);
x_186 = l_Lean_Syntax_mkApp(x_185, x_162);
lean_inc(x_1);
x_187 = l_Lean_Parser_Command_visibility_ofAttrKind(x_1);
x_188 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
x_189 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
x_190 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
x_191 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(x_168);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_168);
lean_ctor_set(x_192, 1, x_191);
x_193 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
x_194 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
x_195 = l_Lean_Elab_Command_mkUnexpander___closed__15;
x_196 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
lean_inc(x_166);
lean_inc(x_165);
x_197 = l_Lean_addMacroScope(x_165, x_196, x_166);
lean_inc(x_168);
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_168);
lean_ctor_set(x_198, 1, x_195);
lean_ctor_set(x_198, 2, x_197);
lean_ctor_set(x_198, 3, x_178);
x_199 = lean_mk_syntax_ident(x_24);
lean_inc(x_199);
lean_inc(x_168);
x_200 = l_Lean_Syntax_node1(x_168, x_172, x_199);
lean_inc(x_168);
x_201 = l_Lean_Syntax_node2(x_168, x_194, x_198, x_200);
lean_inc(x_168);
x_202 = l_Lean_Syntax_node2(x_168, x_193, x_1, x_201);
lean_inc(x_168);
x_203 = l_Lean_Syntax_node1(x_168, x_172, x_202);
x_204 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(x_168);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_168);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_168);
x_206 = l_Lean_Syntax_node3(x_168, x_190, x_192, x_203, x_205);
lean_inc(x_168);
x_207 = l_Lean_Syntax_node1(x_168, x_172, x_206);
lean_inc(x_168);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_168);
lean_ctor_set(x_208, 1, x_188);
x_209 = l_Lean_Elab_Command_mkUnexpander___closed__19;
x_210 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
lean_inc(x_166);
lean_inc(x_165);
x_211 = l_Lean_addMacroScope(x_165, x_210, x_166);
lean_inc(x_168);
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_168);
lean_ctor_set(x_212, 1, x_209);
lean_ctor_set(x_212, 2, x_211);
lean_ctor_set(x_212, 3, x_178);
lean_inc(x_168);
x_213 = l_Lean_Syntax_node2(x_168, x_172, x_212, x_199);
x_214 = l_Lean_Elab_Command_mkUnexpander___closed__22;
x_215 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
lean_inc(x_166);
lean_inc(x_165);
x_216 = l_Lean_addMacroScope(x_165, x_215, x_166);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_18);
lean_ctor_set(x_16, 1, x_178);
lean_ctor_set(x_16, 0, x_217);
lean_inc(x_168);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_168);
lean_ctor_set(x_218, 1, x_214);
lean_ctor_set(x_218, 2, x_216);
lean_ctor_set(x_218, 3, x_16);
x_219 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(x_168);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_168);
lean_ctor_set(x_220, 1, x_219);
x_221 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
x_222 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
lean_inc(x_168);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_168);
lean_ctor_set(x_223, 1, x_221);
x_224 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
x_225 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
x_226 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(x_168);
x_227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_227, 0, x_168);
lean_ctor_set(x_227, 1, x_226);
x_228 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
x_229 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(x_168);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_168);
lean_ctor_set(x_230, 1, x_229);
x_231 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(x_168);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_168);
lean_ctor_set(x_232, 1, x_231);
lean_inc_ref(x_232);
lean_inc_ref(x_230);
lean_inc(x_168);
x_233 = l_Lean_Syntax_node3(x_168, x_228, x_230, x_186, x_232);
lean_inc(x_168);
x_234 = l_Lean_Syntax_node1(x_168, x_172, x_233);
lean_inc(x_168);
x_235 = l_Lean_Syntax_node1(x_168, x_172, x_234);
x_236 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(x_168);
x_237 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_237, 0, x_168);
lean_ctor_set(x_237, 1, x_236);
x_238 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
x_239 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_240 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc(x_166);
lean_inc(x_165);
x_241 = l_Lean_addMacroScope(x_165, x_240, x_166);
x_242 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_18);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_178);
lean_inc(x_168);
x_245 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_245, 0, x_168);
lean_ctor_set(x_245, 1, x_239);
lean_ctor_set(x_245, 2, x_241);
lean_ctor_set(x_245, 3, x_244);
lean_inc_ref(x_232);
lean_inc(x_168);
x_246 = l_Lean_Syntax_node3(x_168, x_228, x_230, x_2, x_232);
lean_inc(x_168);
x_247 = l_Lean_Syntax_node2(x_168, x_172, x_179, x_246);
lean_inc(x_168);
x_248 = l_Lean_Syntax_node2(x_168, x_238, x_245, x_247);
lean_inc_ref(x_237);
lean_inc_ref(x_227);
lean_inc(x_168);
x_249 = l_Lean_Syntax_node4(x_168, x_225, x_227, x_235, x_237, x_248);
x_250 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
x_251 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
lean_inc(x_168);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_168);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_168);
x_253 = l_Lean_Syntax_node1(x_168, x_250, x_252);
lean_inc(x_168);
x_254 = l_Lean_Syntax_node1(x_168, x_172, x_253);
lean_inc(x_168);
x_255 = l_Lean_Syntax_node1(x_168, x_172, x_254);
x_256 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_257 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
lean_inc(x_166);
lean_inc(x_165);
x_258 = l_Lean_addMacroScope(x_165, x_257, x_166);
x_259 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_18);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_178);
lean_inc(x_168);
x_262 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_262, 0, x_168);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set(x_262, 2, x_258);
lean_ctor_set(x_262, 3, x_261);
x_263 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
x_264 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
x_265 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(x_168);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_168);
lean_ctor_set(x_266, 1, x_265);
x_267 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
x_268 = l_Lean_Elab_Command_mkUnexpander___closed__55;
x_269 = lean_box(0);
x_270 = l_Lean_addMacroScope(x_165, x_269, x_166);
x_271 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
lean_inc(x_168);
x_272 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_272, 0, x_168);
lean_ctor_set(x_272, 1, x_268);
lean_ctor_set(x_272, 2, x_270);
lean_ctor_set(x_272, 3, x_271);
lean_inc(x_168);
x_273 = l_Lean_Syntax_node1(x_168, x_267, x_272);
lean_inc(x_168);
x_274 = l_Lean_Syntax_node2(x_168, x_264, x_266, x_273);
lean_inc_ref(x_174);
lean_inc(x_168);
x_275 = l_Lean_Syntax_node3(x_168, x_263, x_274, x_174, x_232);
lean_inc(x_168);
x_276 = l_Lean_Syntax_node1(x_168, x_172, x_275);
lean_inc(x_168);
x_277 = l_Lean_Syntax_node2(x_168, x_238, x_262, x_276);
lean_inc(x_168);
x_278 = l_Lean_Syntax_node4(x_168, x_225, x_227, x_255, x_237, x_277);
lean_inc(x_168);
x_279 = l_Lean_Syntax_node2(x_168, x_172, x_249, x_278);
lean_inc(x_168);
x_280 = l_Lean_Syntax_node1(x_168, x_224, x_279);
lean_inc(x_168);
x_281 = l_Lean_Syntax_node2(x_168, x_222, x_223, x_280);
x_282 = l_Lean_Elab_Command_mkUnexpander___closed__68;
x_283 = lean_array_push(x_282, x_174);
x_284 = lean_array_push(x_283, x_207);
x_285 = lean_array_push(x_284, x_187);
x_286 = lean_array_push(x_285, x_208);
x_287 = lean_array_push(x_286, x_213);
x_288 = lean_array_push(x_287, x_182);
x_289 = lean_array_push(x_288, x_218);
x_290 = lean_array_push(x_289, x_220);
x_291 = lean_array_push(x_290, x_281);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_168);
lean_ctor_set(x_292, 1, x_189);
lean_ctor_set(x_292, 2, x_291);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_163);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_162);
lean_free_object(x_17);
lean_dec(x_24);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_163);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_free_object(x_17);
lean_dec(x_24);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_28);
if (x_297 == 0)
{
return x_28;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_28, 0);
x_299 = lean_ctor_get(x_28, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_28);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
lean_object* x_301; size_t x_302; size_t x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_17, 0);
lean_inc(x_301);
lean_dec(x_17);
x_302 = lean_array_size(x_11);
x_303 = 0;
lean_inc_ref(x_12);
x_304 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_302, x_303, x_11, x_12, x_22);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
x_308 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_305);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_309 = lean_ctor_get(x_12, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_12, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_12, 5);
lean_inc(x_311);
lean_dec_ref(x_12);
x_312 = l_Lean_SourceInfo_fromRef(x_311, x_308);
lean_dec(x_311);
x_313 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
x_314 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
x_315 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(x_312);
x_316 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_316, 0, x_312);
lean_ctor_set(x_316, 1, x_315);
x_317 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_318 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
lean_inc(x_312);
x_319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_319, 0, x_312);
lean_ctor_set(x_319, 1, x_317);
lean_ctor_set(x_319, 2, x_318);
x_320 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_321 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc(x_310);
lean_inc(x_309);
x_322 = l_Lean_addMacroScope(x_309, x_321, x_310);
x_323 = lean_box(0);
lean_inc(x_312);
x_324 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_324, 0, x_312);
lean_ctor_set(x_324, 1, x_320);
lean_ctor_set(x_324, 2, x_322);
lean_ctor_set(x_324, 3, x_323);
x_325 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
x_326 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_312);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_312);
lean_ctor_set(x_327, 1, x_326);
lean_inc(x_312);
x_328 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_328, 0, x_312);
lean_ctor_set(x_328, 1, x_313);
lean_inc_ref(x_327);
lean_inc(x_312);
x_329 = l_Lean_Syntax_node2(x_312, x_325, x_327, x_328);
lean_inc_ref(x_324);
lean_inc_ref(x_319);
lean_inc(x_312);
x_330 = l_Lean_Syntax_node4(x_312, x_314, x_316, x_319, x_324, x_329);
x_331 = l_Lean_Syntax_mkApp(x_330, x_305);
lean_inc(x_1);
x_332 = l_Lean_Parser_Command_visibility_ofAttrKind(x_1);
x_333 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
x_334 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
x_335 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
x_336 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(x_312);
x_337 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_337, 0, x_312);
lean_ctor_set(x_337, 1, x_336);
x_338 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
x_339 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
x_340 = l_Lean_Elab_Command_mkUnexpander___closed__15;
x_341 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
lean_inc(x_310);
lean_inc(x_309);
x_342 = l_Lean_addMacroScope(x_309, x_341, x_310);
lean_inc(x_312);
x_343 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_343, 0, x_312);
lean_ctor_set(x_343, 1, x_340);
lean_ctor_set(x_343, 2, x_342);
lean_ctor_set(x_343, 3, x_323);
x_344 = lean_mk_syntax_ident(x_301);
lean_inc(x_344);
lean_inc(x_312);
x_345 = l_Lean_Syntax_node1(x_312, x_317, x_344);
lean_inc(x_312);
x_346 = l_Lean_Syntax_node2(x_312, x_339, x_343, x_345);
lean_inc(x_312);
x_347 = l_Lean_Syntax_node2(x_312, x_338, x_1, x_346);
lean_inc(x_312);
x_348 = l_Lean_Syntax_node1(x_312, x_317, x_347);
x_349 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(x_312);
x_350 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_350, 0, x_312);
lean_ctor_set(x_350, 1, x_349);
lean_inc(x_312);
x_351 = l_Lean_Syntax_node3(x_312, x_335, x_337, x_348, x_350);
lean_inc(x_312);
x_352 = l_Lean_Syntax_node1(x_312, x_317, x_351);
lean_inc(x_312);
x_353 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_353, 0, x_312);
lean_ctor_set(x_353, 1, x_333);
x_354 = l_Lean_Elab_Command_mkUnexpander___closed__19;
x_355 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
lean_inc(x_310);
lean_inc(x_309);
x_356 = l_Lean_addMacroScope(x_309, x_355, x_310);
lean_inc(x_312);
x_357 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_357, 0, x_312);
lean_ctor_set(x_357, 1, x_354);
lean_ctor_set(x_357, 2, x_356);
lean_ctor_set(x_357, 3, x_323);
lean_inc(x_312);
x_358 = l_Lean_Syntax_node2(x_312, x_317, x_357, x_344);
x_359 = l_Lean_Elab_Command_mkUnexpander___closed__22;
x_360 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
lean_inc(x_310);
lean_inc(x_309);
x_361 = l_Lean_addMacroScope(x_309, x_360, x_310);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_18);
lean_ctor_set(x_16, 1, x_323);
lean_ctor_set(x_16, 0, x_362);
lean_inc(x_312);
x_363 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_363, 0, x_312);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set(x_363, 2, x_361);
lean_ctor_set(x_363, 3, x_16);
x_364 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(x_312);
x_365 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_365, 0, x_312);
lean_ctor_set(x_365, 1, x_364);
x_366 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
x_367 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
lean_inc(x_312);
x_368 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_368, 0, x_312);
lean_ctor_set(x_368, 1, x_366);
x_369 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
x_370 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
x_371 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(x_312);
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_312);
lean_ctor_set(x_372, 1, x_371);
x_373 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
x_374 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(x_312);
x_375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_375, 0, x_312);
lean_ctor_set(x_375, 1, x_374);
x_376 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(x_312);
x_377 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_377, 0, x_312);
lean_ctor_set(x_377, 1, x_376);
lean_inc_ref(x_377);
lean_inc_ref(x_375);
lean_inc(x_312);
x_378 = l_Lean_Syntax_node3(x_312, x_373, x_375, x_331, x_377);
lean_inc(x_312);
x_379 = l_Lean_Syntax_node1(x_312, x_317, x_378);
lean_inc(x_312);
x_380 = l_Lean_Syntax_node1(x_312, x_317, x_379);
x_381 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(x_312);
x_382 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_382, 0, x_312);
lean_ctor_set(x_382, 1, x_381);
x_383 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
x_384 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_385 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc(x_310);
lean_inc(x_309);
x_386 = l_Lean_addMacroScope(x_309, x_385, x_310);
x_387 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_18);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_323);
lean_inc(x_312);
x_390 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_390, 0, x_312);
lean_ctor_set(x_390, 1, x_384);
lean_ctor_set(x_390, 2, x_386);
lean_ctor_set(x_390, 3, x_389);
lean_inc_ref(x_377);
lean_inc(x_312);
x_391 = l_Lean_Syntax_node3(x_312, x_373, x_375, x_2, x_377);
lean_inc(x_312);
x_392 = l_Lean_Syntax_node2(x_312, x_317, x_324, x_391);
lean_inc(x_312);
x_393 = l_Lean_Syntax_node2(x_312, x_383, x_390, x_392);
lean_inc_ref(x_382);
lean_inc_ref(x_372);
lean_inc(x_312);
x_394 = l_Lean_Syntax_node4(x_312, x_370, x_372, x_380, x_382, x_393);
x_395 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
x_396 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
lean_inc(x_312);
x_397 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_397, 0, x_312);
lean_ctor_set(x_397, 1, x_396);
lean_inc(x_312);
x_398 = l_Lean_Syntax_node1(x_312, x_395, x_397);
lean_inc(x_312);
x_399 = l_Lean_Syntax_node1(x_312, x_317, x_398);
lean_inc(x_312);
x_400 = l_Lean_Syntax_node1(x_312, x_317, x_399);
x_401 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_402 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
lean_inc(x_310);
lean_inc(x_309);
x_403 = l_Lean_addMacroScope(x_309, x_402, x_310);
x_404 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_18);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_323);
lean_inc(x_312);
x_407 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_407, 0, x_312);
lean_ctor_set(x_407, 1, x_401);
lean_ctor_set(x_407, 2, x_403);
lean_ctor_set(x_407, 3, x_406);
x_408 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
x_409 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
x_410 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(x_312);
x_411 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_411, 0, x_312);
lean_ctor_set(x_411, 1, x_410);
x_412 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
x_413 = l_Lean_Elab_Command_mkUnexpander___closed__55;
x_414 = lean_box(0);
x_415 = l_Lean_addMacroScope(x_309, x_414, x_310);
x_416 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
lean_inc(x_312);
x_417 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_417, 0, x_312);
lean_ctor_set(x_417, 1, x_413);
lean_ctor_set(x_417, 2, x_415);
lean_ctor_set(x_417, 3, x_416);
lean_inc(x_312);
x_418 = l_Lean_Syntax_node1(x_312, x_412, x_417);
lean_inc(x_312);
x_419 = l_Lean_Syntax_node2(x_312, x_409, x_411, x_418);
lean_inc_ref(x_319);
lean_inc(x_312);
x_420 = l_Lean_Syntax_node3(x_312, x_408, x_419, x_319, x_377);
lean_inc(x_312);
x_421 = l_Lean_Syntax_node1(x_312, x_317, x_420);
lean_inc(x_312);
x_422 = l_Lean_Syntax_node2(x_312, x_383, x_407, x_421);
lean_inc(x_312);
x_423 = l_Lean_Syntax_node4(x_312, x_370, x_372, x_400, x_382, x_422);
lean_inc(x_312);
x_424 = l_Lean_Syntax_node2(x_312, x_317, x_394, x_423);
lean_inc(x_312);
x_425 = l_Lean_Syntax_node1(x_312, x_369, x_424);
lean_inc(x_312);
x_426 = l_Lean_Syntax_node2(x_312, x_367, x_368, x_425);
x_427 = l_Lean_Elab_Command_mkUnexpander___closed__68;
x_428 = lean_array_push(x_427, x_319);
x_429 = lean_array_push(x_428, x_352);
x_430 = lean_array_push(x_429, x_332);
x_431 = lean_array_push(x_430, x_353);
x_432 = lean_array_push(x_431, x_358);
x_433 = lean_array_push(x_432, x_327);
x_434 = lean_array_push(x_433, x_363);
x_435 = lean_array_push(x_434, x_365);
x_436 = lean_array_push(x_435, x_426);
x_437 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_437, 0, x_312);
lean_ctor_set(x_437, 1, x_334);
lean_ctor_set(x_437, 2, x_436);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
if (lean_is_scalar(x_307)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_307;
}
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_306);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_305);
lean_dec(x_301);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_440 = lean_box(0);
if (lean_is_scalar(x_307)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_307;
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_306);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_301);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_442 = lean_ctor_get(x_304, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_304, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_444 = x_304;
} else {
 lean_dec_ref(x_304);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
}
else
{
lean_object* x_446; 
lean_free_object(x_16);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_446 = lean_ctor_get(x_15, 1);
lean_inc(x_446);
lean_dec_ref(x_15);
x_6 = x_446;
goto block_9;
}
}
else
{
lean_object* x_447; 
x_447 = lean_ctor_get(x_16, 1);
lean_inc(x_447);
lean_dec(x_16);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; size_t x_451; size_t x_452; lean_object* x_453; 
x_448 = lean_ctor_get(x_15, 1);
lean_inc(x_448);
lean_dec_ref(x_15);
x_449 = lean_ctor_get(x_17, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_450 = x_17;
} else {
 lean_dec_ref(x_17);
 x_450 = lean_box(0);
}
x_451 = lean_array_size(x_11);
x_452 = 0;
lean_inc_ref(x_12);
x_453 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(x_451, x_452, x_11, x_12, x_448);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
x_457 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_454);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_458 = lean_ctor_get(x_12, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_12, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_12, 5);
lean_inc(x_460);
lean_dec_ref(x_12);
x_461 = l_Lean_SourceInfo_fromRef(x_460, x_457);
lean_dec(x_460);
x_462 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
x_463 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
x_464 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(x_461);
if (lean_is_scalar(x_450)) {
 x_465 = lean_alloc_ctor(2, 2, 0);
} else {
 x_465 = x_450;
 lean_ctor_set_tag(x_465, 2);
}
lean_ctor_set(x_465, 0, x_461);
lean_ctor_set(x_465, 1, x_464);
x_466 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_467 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
lean_inc(x_461);
x_468 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_468, 0, x_461);
lean_ctor_set(x_468, 1, x_466);
lean_ctor_set(x_468, 2, x_467);
x_469 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_470 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc(x_459);
lean_inc(x_458);
x_471 = l_Lean_addMacroScope(x_458, x_470, x_459);
x_472 = lean_box(0);
lean_inc(x_461);
x_473 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_473, 0, x_461);
lean_ctor_set(x_473, 1, x_469);
lean_ctor_set(x_473, 2, x_471);
lean_ctor_set(x_473, 3, x_472);
x_474 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
x_475 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_461);
x_476 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_476, 0, x_461);
lean_ctor_set(x_476, 1, x_475);
lean_inc(x_461);
x_477 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_477, 0, x_461);
lean_ctor_set(x_477, 1, x_462);
lean_inc_ref(x_476);
lean_inc(x_461);
x_478 = l_Lean_Syntax_node2(x_461, x_474, x_476, x_477);
lean_inc_ref(x_473);
lean_inc_ref(x_468);
lean_inc(x_461);
x_479 = l_Lean_Syntax_node4(x_461, x_463, x_465, x_468, x_473, x_478);
x_480 = l_Lean_Syntax_mkApp(x_479, x_454);
lean_inc(x_1);
x_481 = l_Lean_Parser_Command_visibility_ofAttrKind(x_1);
x_482 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
x_483 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
x_484 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
x_485 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(x_461);
x_486 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_486, 0, x_461);
lean_ctor_set(x_486, 1, x_485);
x_487 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
x_488 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
x_489 = l_Lean_Elab_Command_mkUnexpander___closed__15;
x_490 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
lean_inc(x_459);
lean_inc(x_458);
x_491 = l_Lean_addMacroScope(x_458, x_490, x_459);
lean_inc(x_461);
x_492 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_492, 0, x_461);
lean_ctor_set(x_492, 1, x_489);
lean_ctor_set(x_492, 2, x_491);
lean_ctor_set(x_492, 3, x_472);
x_493 = lean_mk_syntax_ident(x_449);
lean_inc(x_493);
lean_inc(x_461);
x_494 = l_Lean_Syntax_node1(x_461, x_466, x_493);
lean_inc(x_461);
x_495 = l_Lean_Syntax_node2(x_461, x_488, x_492, x_494);
lean_inc(x_461);
x_496 = l_Lean_Syntax_node2(x_461, x_487, x_1, x_495);
lean_inc(x_461);
x_497 = l_Lean_Syntax_node1(x_461, x_466, x_496);
x_498 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(x_461);
x_499 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_499, 0, x_461);
lean_ctor_set(x_499, 1, x_498);
lean_inc(x_461);
x_500 = l_Lean_Syntax_node3(x_461, x_484, x_486, x_497, x_499);
lean_inc(x_461);
x_501 = l_Lean_Syntax_node1(x_461, x_466, x_500);
lean_inc(x_461);
x_502 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_502, 0, x_461);
lean_ctor_set(x_502, 1, x_482);
x_503 = l_Lean_Elab_Command_mkUnexpander___closed__19;
x_504 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
lean_inc(x_459);
lean_inc(x_458);
x_505 = l_Lean_addMacroScope(x_458, x_504, x_459);
lean_inc(x_461);
x_506 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_506, 0, x_461);
lean_ctor_set(x_506, 1, x_503);
lean_ctor_set(x_506, 2, x_505);
lean_ctor_set(x_506, 3, x_472);
lean_inc(x_461);
x_507 = l_Lean_Syntax_node2(x_461, x_466, x_506, x_493);
x_508 = l_Lean_Elab_Command_mkUnexpander___closed__22;
x_509 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
lean_inc(x_459);
lean_inc(x_458);
x_510 = l_Lean_addMacroScope(x_458, x_509, x_459);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_18);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_472);
lean_inc(x_461);
x_513 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_513, 0, x_461);
lean_ctor_set(x_513, 1, x_508);
lean_ctor_set(x_513, 2, x_510);
lean_ctor_set(x_513, 3, x_512);
x_514 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(x_461);
x_515 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_515, 0, x_461);
lean_ctor_set(x_515, 1, x_514);
x_516 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
x_517 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
lean_inc(x_461);
x_518 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_518, 0, x_461);
lean_ctor_set(x_518, 1, x_516);
x_519 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
x_520 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
x_521 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(x_461);
x_522 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_522, 0, x_461);
lean_ctor_set(x_522, 1, x_521);
x_523 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
x_524 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(x_461);
x_525 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_525, 0, x_461);
lean_ctor_set(x_525, 1, x_524);
x_526 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(x_461);
x_527 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_527, 0, x_461);
lean_ctor_set(x_527, 1, x_526);
lean_inc_ref(x_527);
lean_inc_ref(x_525);
lean_inc(x_461);
x_528 = l_Lean_Syntax_node3(x_461, x_523, x_525, x_480, x_527);
lean_inc(x_461);
x_529 = l_Lean_Syntax_node1(x_461, x_466, x_528);
lean_inc(x_461);
x_530 = l_Lean_Syntax_node1(x_461, x_466, x_529);
x_531 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(x_461);
x_532 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_532, 0, x_461);
lean_ctor_set(x_532, 1, x_531);
x_533 = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
x_534 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_535 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc(x_459);
lean_inc(x_458);
x_536 = l_Lean_addMacroScope(x_458, x_535, x_459);
x_537 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_18);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_472);
lean_inc(x_461);
x_540 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_540, 0, x_461);
lean_ctor_set(x_540, 1, x_534);
lean_ctor_set(x_540, 2, x_536);
lean_ctor_set(x_540, 3, x_539);
lean_inc_ref(x_527);
lean_inc(x_461);
x_541 = l_Lean_Syntax_node3(x_461, x_523, x_525, x_2, x_527);
lean_inc(x_461);
x_542 = l_Lean_Syntax_node2(x_461, x_466, x_473, x_541);
lean_inc(x_461);
x_543 = l_Lean_Syntax_node2(x_461, x_533, x_540, x_542);
lean_inc_ref(x_532);
lean_inc_ref(x_522);
lean_inc(x_461);
x_544 = l_Lean_Syntax_node4(x_461, x_520, x_522, x_530, x_532, x_543);
x_545 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
x_546 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
lean_inc(x_461);
x_547 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_547, 0, x_461);
lean_ctor_set(x_547, 1, x_546);
lean_inc(x_461);
x_548 = l_Lean_Syntax_node1(x_461, x_545, x_547);
lean_inc(x_461);
x_549 = l_Lean_Syntax_node1(x_461, x_466, x_548);
lean_inc(x_461);
x_550 = l_Lean_Syntax_node1(x_461, x_466, x_549);
x_551 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_552 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
lean_inc(x_459);
lean_inc(x_458);
x_553 = l_Lean_addMacroScope(x_458, x_552, x_459);
x_554 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_18);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_472);
lean_inc(x_461);
x_557 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_557, 0, x_461);
lean_ctor_set(x_557, 1, x_551);
lean_ctor_set(x_557, 2, x_553);
lean_ctor_set(x_557, 3, x_556);
x_558 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
x_559 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
x_560 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(x_461);
x_561 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_561, 0, x_461);
lean_ctor_set(x_561, 1, x_560);
x_562 = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
x_563 = l_Lean_Elab_Command_mkUnexpander___closed__55;
x_564 = lean_box(0);
x_565 = l_Lean_addMacroScope(x_458, x_564, x_459);
x_566 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
lean_inc(x_461);
x_567 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_567, 0, x_461);
lean_ctor_set(x_567, 1, x_563);
lean_ctor_set(x_567, 2, x_565);
lean_ctor_set(x_567, 3, x_566);
lean_inc(x_461);
x_568 = l_Lean_Syntax_node1(x_461, x_562, x_567);
lean_inc(x_461);
x_569 = l_Lean_Syntax_node2(x_461, x_559, x_561, x_568);
lean_inc_ref(x_468);
lean_inc(x_461);
x_570 = l_Lean_Syntax_node3(x_461, x_558, x_569, x_468, x_527);
lean_inc(x_461);
x_571 = l_Lean_Syntax_node1(x_461, x_466, x_570);
lean_inc(x_461);
x_572 = l_Lean_Syntax_node2(x_461, x_533, x_557, x_571);
lean_inc(x_461);
x_573 = l_Lean_Syntax_node4(x_461, x_520, x_522, x_550, x_532, x_572);
lean_inc(x_461);
x_574 = l_Lean_Syntax_node2(x_461, x_466, x_544, x_573);
lean_inc(x_461);
x_575 = l_Lean_Syntax_node1(x_461, x_519, x_574);
lean_inc(x_461);
x_576 = l_Lean_Syntax_node2(x_461, x_517, x_518, x_575);
x_577 = l_Lean_Elab_Command_mkUnexpander___closed__68;
x_578 = lean_array_push(x_577, x_468);
x_579 = lean_array_push(x_578, x_501);
x_580 = lean_array_push(x_579, x_481);
x_581 = lean_array_push(x_580, x_502);
x_582 = lean_array_push(x_581, x_507);
x_583 = lean_array_push(x_582, x_476);
x_584 = lean_array_push(x_583, x_513);
x_585 = lean_array_push(x_584, x_515);
x_586 = lean_array_push(x_585, x_576);
x_587 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_587, 0, x_461);
lean_ctor_set(x_587, 1, x_483);
lean_ctor_set(x_587, 2, x_586);
x_588 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_588, 0, x_587);
if (lean_is_scalar(x_456)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_456;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_455);
return x_589;
}
else
{
lean_object* x_590; lean_object* x_591; 
lean_dec(x_454);
lean_dec(x_450);
lean_dec(x_449);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_590 = lean_box(0);
if (lean_is_scalar(x_456)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_456;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_455);
return x_591;
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_592 = lean_ctor_get(x_453, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_453, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_594 = x_453;
} else {
 lean_dec_ref(x_453);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
}
else
{
lean_object* x_596; 
lean_dec(x_447);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_596 = lean_ctor_get(x_15, 1);
lean_inc(x_596);
lean_dec_ref(x_15);
x_6 = x_596;
goto block_9;
}
}
}
else
{
lean_object* x_597; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_597 = lean_ctor_get(x_15, 1);
lean_inc(x_597);
lean_dec_ref(x_15);
x_6 = x_597;
goto block_9;
}
}
else
{
lean_object* x_598; 
lean_dec(x_16);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_598 = lean_ctor_get(x_15, 1);
lean_inc(x_598);
lean_dec_ref(x_15);
x_6 = x_598;
goto block_9;
}
}
else
{
uint8_t x_599; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_15);
if (x_599 == 0)
{
return x_15;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_15, 0);
x_601 = lean_ctor_get(x_15, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_15);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_ctor_get(x_2, 6);
x_11 = lean_ctor_get(x_2, 7);
x_12 = lean_ctor_get(x_2, 8);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_16 = lean_ctor_get(x_2, 9);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set(x_17, 4, x_8);
lean_ctor_set(x_17, 5, x_9);
lean_ctor_set(x_17, 6, x_10);
lean_ctor_set(x_17, 7, x_11);
lean_ctor_set(x_17, 8, x_12);
lean_ctor_set(x_17, 9, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*10, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*10 + 1, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*10 + 2, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_3);
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_7, x_5);
if (x_6 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
x_10 = l_Lean_Name_isPrefixOf(x_9, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_10);
return x_1;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_3);
lean_inc(x_2);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_13, x_11);
if (x_12 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
x_16 = l_Lean_Name_isPrefixOf(x_15, x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc_ref(x_4);
x_9 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_15;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_array_uset(x_3, x_2, x_5);
x_8 = l_Lean_Syntax_getArg(x_6, x_5);
lean_dec(x_6);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_9);
x_2 = x_14;
x_3 = x_15;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_1);
x_19 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofSyntax(x_16);
x_22 = l_Lean_indentD(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(x_23, x_2);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_ofSyntax(x_26);
x_32 = l_Lean_indentD(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(x_33, x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2;
x_12 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__6;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(x_9, x_7, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 7);
lean_dec(x_9);
x_10 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 7, x_10);
x_11 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_3, 6);
x_19 = lean_ctor_get(x_3, 8);
x_20 = lean_ctor_get(x_3, 9);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_22 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_22);
lean_ctor_set(x_23, 8, x_19);
lean_ctor_set(x_23, 9, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_21);
x_24 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(x_2, x_23, x_4);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4;
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_inheritedTraceOptions;
x_5 = lean_st_ref_get(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
x_15 = l_Lean_Name_append(x_14, x_1);
x_16 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_5, x_10, x_15);
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(x_2, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_st_ref_take(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; double x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0;
x_17 = 0;
x_18 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_17);
x_20 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1;
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_PersistentArray_push___redArg(x_15, x_22);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_st_ref_set(x_4, x_11);
x_25 = lean_box(0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
uint64_t x_26; lean_object* x_27; double x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0;
x_29 = 0;
x_30 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
x_31 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_float(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_float(x_31, sizeof(void*)*2 + 8, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_29);
x_32 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1;
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PersistentArray_push___redArg(x_27, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_26);
lean_ctor_set(x_11, 9, x_36);
x_37 = lean_st_ref_set(x_4, x_11);
x_38 = lean_box(0);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; double x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_11, 9);
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
x_42 = lean_ctor_get(x_11, 2);
x_43 = lean_ctor_get(x_11, 3);
x_44 = lean_ctor_get(x_11, 4);
x_45 = lean_ctor_get(x_11, 5);
x_46 = lean_ctor_get(x_11, 6);
x_47 = lean_ctor_get(x_11, 7);
x_48 = lean_ctor_get(x_11, 8);
x_49 = lean_ctor_get(x_11, 10);
lean_inc(x_49);
lean_inc(x_39);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_50 = lean_ctor_get_uint64(x_39, sizeof(void*)*1);
x_51 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
x_53 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0;
x_54 = 0;
x_55 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
x_56 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_float(x_56, sizeof(void*)*2, x_53);
lean_ctor_set_float(x_56, sizeof(void*)*2 + 8, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 16, x_54);
x_57 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1;
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_10);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_PersistentArray_push___redArg(x_51, x_59);
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 1, 8);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_50);
x_62 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_62, 0, x_40);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_62, 2, x_42);
lean_ctor_set(x_62, 3, x_43);
lean_ctor_set(x_62, 4, x_44);
lean_ctor_set(x_62, 5, x_45);
lean_ctor_set(x_62, 6, x_46);
lean_ctor_set(x_62, 7, x_47);
lean_ctor_set(x_62, 8, x_48);
lean_ctor_set(x_62, 9, x_61);
lean_ctor_set(x_62, 10, x_49);
x_63 = lean_st_ref_set(x_4, x_62);
x_64 = lean_box(0);
lean_ctor_set(x_8, 0, x_64);
return x_8;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; double x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
lean_dec(x_8);
x_66 = lean_st_ref_take(x_4);
x_67 = lean_ctor_get(x_66, 9);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_66, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 6);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_66, 7);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_66, 8);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_66, 10);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 lean_ctor_release(x_66, 5);
 lean_ctor_release(x_66, 6);
 lean_ctor_release(x_66, 7);
 lean_ctor_release(x_66, 8);
 lean_ctor_release(x_66, 9);
 lean_ctor_release(x_66, 10);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get_uint64(x_67, sizeof(void*)*1);
x_80 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_80);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_81 = x_67;
} else {
 lean_dec_ref(x_67);
 x_81 = lean_box(0);
}
x_82 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0;
x_83 = 0;
x_84 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
x_85 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_float(x_85, sizeof(void*)*2, x_82);
lean_ctor_set_float(x_85, sizeof(void*)*2 + 8, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 16, x_83);
x_86 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1;
x_87 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_65);
lean_ctor_set(x_87, 2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_7);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_PersistentArray_push___redArg(x_80, x_88);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 1, 8);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_uint64(x_90, sizeof(void*)*1, x_79);
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 11, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_70);
lean_ctor_set(x_91, 3, x_71);
lean_ctor_set(x_91, 4, x_72);
lean_ctor_set(x_91, 5, x_73);
lean_ctor_set(x_91, 6, x_74);
lean_ctor_set(x_91, 7, x_75);
lean_ctor_set(x_91, 8, x_76);
lean_ctor_set(x_91, 9, x_90);
lean_ctor_set(x_91, 10, x_77);
x_92 = lean_st_ref_set(x_4, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_6);
if (x_95 == 0)
{
return x_6;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_6, 0);
lean_inc(x_96);
lean_dec(x_6);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; uint8_t x_47; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2;
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_2);
x_14 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_15 = lean_box(1);
x_16 = lean_box(0);
x_46 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_12, x_14, x_11, x_15, x_16);
x_47 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(x_46, x_13);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_56; lean_object* x_57; uint8_t x_70; 
x_48 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4));
x_49 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(x_48, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_70 = lean_unbox(x_50);
lean_dec(x_50);
if (x_70 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_17 = x_5;
x_18 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11;
if (x_9 == 0)
{
lean_object* x_80; 
x_80 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16));
x_72 = x_80;
goto block_79;
}
else
{
lean_object* x_81; 
x_81 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17));
x_72 = x_81;
goto block_79;
}
block_79:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l_Lean_stringToMessageData(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
if (x_2 == 0)
{
lean_object* x_77; 
x_77 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14));
x_56 = x_76;
x_57 = x_77;
goto block_69;
}
else
{
lean_object* x_78; 
x_78 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15));
x_56 = x_76;
x_57 = x_78;
goto block_69;
}
}
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(x_48, x_53, x_4, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_17 = x_5;
x_18 = lean_box(0);
goto block_45;
}
else
{
lean_dec_ref(x_13);
return x_54;
}
}
block_69:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = l_Lean_stringToMessageData(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_MessageData_ofName(x_1);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Name_isAnonymous(x_3);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8;
x_66 = l_Lean_MessageData_ofName(x_3);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_51 = x_63;
x_52 = x_67;
goto block_55;
}
else
{
lean_object* x_68; 
lean_dec(x_3);
x_68 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9;
x_51 = x_63;
x_52 = x_68;
goto block_55;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
block_45:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_st_ref_take(x_17);
x_20 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_20);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_14, x_22, x_13, x_23, x_16);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_24);
x_25 = lean_st_ref_set(x_17, x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
x_30 = lean_ctor_get(x_19, 2);
x_31 = lean_ctor_get(x_19, 3);
x_32 = lean_ctor_get(x_19, 4);
x_33 = lean_ctor_get(x_19, 5);
x_34 = lean_ctor_get(x_19, 6);
x_35 = lean_ctor_get(x_19, 7);
x_36 = lean_ctor_get(x_19, 8);
x_37 = lean_ctor_get(x_19, 9);
x_38 = lean_ctor_get(x_19, 10);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_39 = lean_ctor_get(x_20, 2);
lean_inc(x_39);
lean_dec_ref(x_20);
x_40 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_14, x_28, x_13, x_39, x_16);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set(x_41, 10, x_38);
x_42 = lean_st_ref_set(x_17, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_12 = l_Lean_Environment_header(x_1);
x_13 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_instInhabitedEffectiveImport_default;
x_15 = lean_array_uget(x_3, x_5);
x_16 = lean_array_get(x_14, x_13, x_15);
lean_dec(x_15);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = 0;
lean_inc(x_2);
x_20 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(x_18, x_19, x_2, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_20);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_21; 
x_6 = lean_st_ref_get(x_4);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
lean_dec(x_6);
x_21 = l_Lean_Environment_getModuleIdxFor_x3f(x_10, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Environment_header(x_10);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_lt(x_22, x_25);
if (x_26 == 0)
{
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_st_ref_get(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec(x_27);
x_29 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2;
x_30 = lean_array_fget(x_24, x_22);
lean_dec(x_22);
lean_dec_ref(x_24);
if (x_2 == 0)
{
lean_dec_ref(x_28);
x_31 = x_2;
goto block_42;
}
else
{
uint8_t x_43; 
lean_inc(x_1);
x_43 = l_Lean_isMarkedMeta(x_28, x_1);
if (x_43 == 0)
{
x_31 = x_2;
goto block_42;
}
else
{
uint8_t x_44; 
x_44 = 0;
x_31 = x_44;
goto block_42;
}
}
block_42:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc(x_1);
x_34 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(x_33, x_31, x_1, x_3, x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_34);
x_35 = l_Lean_indirectModUseExt;
x_36 = lean_box(1);
x_37 = lean_box(0);
lean_inc_ref(x_10);
x_38 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_29, x_35, x_10, x_36, x_37);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(x_38, x_1);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3;
x_11 = lean_box(0);
x_12 = x_40;
goto block_20;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_11 = lean_box(0);
x_12 = x_41;
goto block_20;
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_1);
return x_34;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_20:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(x_10, x_1, x_12, x_14, x_15, x_13, x_3, x_4);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = 1;
x_10 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(x_7, x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_8;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_15, x_16);
lean_dec_ref(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_20, x_16);
lean_dec_ref(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec_ref(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_15, x_22);
lean_dec_ref(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_27, x_22);
lean_dec_ref(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_34, x_31);
lean_dec_ref(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec_ref(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_40, x_36);
lean_dec_ref(x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
return x_5;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_9);
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(x_9, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_10);
x_16 = l_Lean_MessageData_ofFormat(x_11);
x_17 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(x_9, x_16, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
return x_17;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_10);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(x_9, x_23, x_2, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_instInhabitedScope_default;
x_10 = l_List_head_x21___redArg(x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_24, 0, x_6);
lean_inc_ref(x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_25, 0, x_6);
lean_inc(x_14);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_26, 0, x_14);
lean_inc(x_17);
lean_inc(x_14);
lean_inc_ref(x_6);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_17);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_14);
lean_closure_set(x_28, 3, x_17);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(x_3);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_30 = x_93;
x_31 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_23, 0);
lean_inc(x_94);
x_30 = x_94;
x_31 = lean_box(0);
goto block_91;
}
block_91:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_st_ref_get(x_3);
x_33 = lean_ctor_get(x_32, 5);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_3);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_22);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_22);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_19);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_apply_2(x_1, x_36, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(x_44, x_45, x_2, x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
lean_dec_ref(x_46);
x_47 = lean_st_ref_take(x_3);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 4);
lean_dec(x_49);
lean_ctor_set(x_47, 4, x_42);
x_50 = lean_st_ref_set(x_3, x_47);
x_51 = l_List_reverse___redArg(x_43);
x_52 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(x_51, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_41);
return x_52;
}
else
{
lean_object* x_55; 
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_41);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_41);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
x_61 = lean_ctor_get(x_47, 2);
x_62 = lean_ctor_get(x_47, 3);
x_63 = lean_ctor_get(x_47, 5);
x_64 = lean_ctor_get(x_47, 6);
x_65 = lean_ctor_get(x_47, 7);
x_66 = lean_ctor_get(x_47, 8);
x_67 = lean_ctor_get(x_47, 9);
x_68 = lean_ctor_get(x_47, 10);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_69 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_60);
lean_ctor_set(x_69, 2, x_61);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_42);
lean_ctor_set(x_69, 5, x_63);
lean_ctor_set(x_69, 6, x_64);
lean_ctor_set(x_69, 7, x_65);
lean_ctor_set(x_69, 8, x_66);
lean_ctor_set(x_69, 9, x_67);
lean_ctor_set(x_69, 10, x_68);
x_70 = lean_st_ref_set(x_3, x_69);
x_71 = l_List_reverse___redArg(x_43);
x_72 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(x_71, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_73 = x_72;
} else {
 lean_dec_ref(x_72);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_41);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_41);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_2);
x_78 = !lean_is_exclusive(x_46);
if (x_78 == 0)
{
return x_46;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_46, 0);
lean_inc(x_79);
lean_dec(x_46);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_39, 0);
lean_inc(x_81);
lean_dec_ref(x_39);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_81);
x_84 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
x_85 = lean_string_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_83);
x_87 = l_Lean_MessageData_ofFormat(x_86);
x_88 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(x_82, x_87, x_2, x_3);
lean_dec(x_82);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec_ref(x_83);
lean_dec_ref(x_2);
x_89 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(x_82);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec_ref(x_2);
x_90 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_90;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_20);
if (x_95 == 0)
{
return x_20;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_20, 0);
lean_inc(x_96);
lean_dec(x_20);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_18);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_18, 0);
lean_inc(x_99);
lean_dec(x_18);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_101 = !lean_is_exclusive(x_15);
if (x_101 == 0)
{
return x_15;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_15, 0);
lean_inc(x_102);
lean_dec(x_15);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_104 = !lean_is_exclusive(x_12);
if (x_104 == 0)
{
return x_12;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_12, 0);
lean_inc(x_105);
lean_dec(x_12);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNotation___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNotation___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
x_28 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
x_29 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(x_1);
x_30 = l_Lean_Syntax_isOfKind(x_1, x_29);
if (x_30 == 0)
{
lean_object* x_126; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_126 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; size_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; size_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; size_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; size_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_466; uint8_t x_467; 
x_127 = lean_unsigned_to_nat(0u);
x_466 = l_Lean_Syntax_getArg(x_1, x_127);
x_467 = l_Lean_Syntax_isNone(x_466);
if (x_467 == 0)
{
lean_object* x_468; uint8_t x_469; 
x_468 = lean_unsigned_to_nat(1u);
lean_inc(x_466);
x_469 = l_Lean_Syntax_matchesNull(x_466, x_468);
if (x_469 == 0)
{
lean_object* x_470; 
lean_dec(x_466);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_470 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_471 = l_Lean_Syntax_getArg(x_466, x_127);
lean_dec(x_466);
x_472 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__16));
lean_inc(x_471);
x_473 = l_Lean_Syntax_isOfKind(x_471, x_472);
if (x_473 == 0)
{
lean_object* x_474; 
lean_dec(x_471);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_474 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_474;
}
else
{
lean_object* x_475; 
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_471);
x_448 = x_475;
x_449 = x_2;
x_450 = x_3;
x_451 = lean_box(0);
goto block_465;
}
}
}
else
{
lean_object* x_476; 
lean_dec(x_466);
x_476 = lean_box(0);
x_448 = x_476;
x_449 = x_2;
x_450 = x_3;
x_451 = lean_box(0);
goto block_465;
}
block_196:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; size_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc_ref(x_146);
x_149 = l_Array_append___redArg(x_146, x_148);
lean_dec_ref(x_148);
lean_inc(x_136);
lean_inc(x_134);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_134);
lean_ctor_set(x_150, 1, x_136);
lean_ctor_set(x_150, 2, x_149);
x_151 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
x_152 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(x_134);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_134);
lean_ctor_set(x_153, 1, x_152);
x_154 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
lean_inc(x_134);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_134);
lean_ctor_set(x_155, 1, x_154);
x_156 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(x_134);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_134);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Nat_reprFast(x_132);
x_159 = lean_box(2);
x_160 = l_Lean_Syntax_mkNumLit(x_158, x_159);
x_161 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(x_134);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_134);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_134);
x_163 = l_Lean_Syntax_node5(x_134, x_151, x_153, x_155, x_157, x_160, x_162);
lean_inc(x_136);
lean_inc(x_134);
x_164 = l_Lean_Syntax_node1(x_134, x_136, x_163);
x_165 = lean_array_size(x_135);
x_166 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(x_165, x_131, x_135);
lean_inc_ref(x_146);
x_167 = l_Array_append___redArg(x_146, x_166);
lean_dec_ref(x_166);
lean_inc(x_136);
lean_inc(x_134);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_134);
lean_ctor_set(x_168, 1, x_136);
lean_ctor_set(x_168, 2, x_167);
x_169 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_134);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_134);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Elab_Command_elabNotation___closed__9;
x_172 = lean_array_push(x_171, x_137);
x_173 = lean_array_push(x_172, x_138);
lean_inc(x_142);
x_174 = lean_array_push(x_173, x_142);
x_175 = lean_array_push(x_174, x_147);
x_176 = lean_array_push(x_175, x_143);
x_177 = lean_array_push(x_176, x_150);
x_178 = lean_array_push(x_177, x_164);
x_179 = lean_array_push(x_178, x_168);
x_180 = lean_array_push(x_179, x_170);
x_181 = lean_array_push(x_180, x_140);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_134);
lean_ctor_set(x_182, 1, x_133);
lean_ctor_set(x_182, 2, x_181);
lean_inc(x_130);
lean_inc_ref(x_141);
x_183 = l_Lean_Elab_Command_elabSyntax(x_182, x_141, x_130);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_array_get_size(x_129);
x_186 = l_Lean_Elab_Command_mkUnexpander___closed__69;
x_187 = lean_nat_dec_lt(x_127, x_185);
if (x_187 == 0)
{
x_85 = x_128;
x_86 = x_129;
x_87 = x_159;
x_88 = x_131;
x_89 = x_130;
x_90 = x_136;
x_91 = lean_box(0);
x_92 = x_139;
x_93 = x_141;
x_94 = x_161;
x_95 = x_142;
x_96 = x_144;
x_97 = x_146;
x_98 = x_184;
x_99 = x_186;
goto block_125;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_185, x_185);
if (x_188 == 0)
{
if (x_187 == 0)
{
x_85 = x_128;
x_86 = x_129;
x_87 = x_159;
x_88 = x_131;
x_89 = x_130;
x_90 = x_136;
x_91 = lean_box(0);
x_92 = x_139;
x_93 = x_141;
x_94 = x_161;
x_95 = x_142;
x_96 = x_144;
x_97 = x_146;
x_98 = x_184;
x_99 = x_186;
goto block_125;
}
else
{
size_t x_189; lean_object* x_190; 
x_189 = lean_usize_of_nat(x_185);
x_190 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(x_129, x_131, x_189, x_186);
x_85 = x_128;
x_86 = x_129;
x_87 = x_159;
x_88 = x_131;
x_89 = x_130;
x_90 = x_136;
x_91 = lean_box(0);
x_92 = x_139;
x_93 = x_141;
x_94 = x_161;
x_95 = x_142;
x_96 = x_144;
x_97 = x_146;
x_98 = x_184;
x_99 = x_190;
goto block_125;
}
}
else
{
size_t x_191; lean_object* x_192; 
x_191 = lean_usize_of_nat(x_185);
x_192 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(x_129, x_131, x_191, x_186);
x_85 = x_128;
x_86 = x_129;
x_87 = x_159;
x_88 = x_131;
x_89 = x_130;
x_90 = x_136;
x_91 = lean_box(0);
x_92 = x_139;
x_93 = x_141;
x_94 = x_161;
x_95 = x_142;
x_96 = x_144;
x_97 = x_146;
x_98 = x_184;
x_99 = x_192;
goto block_125;
}
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_146);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_139);
lean_dec(x_136);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
x_193 = !lean_is_exclusive(x_183);
if (x_193 == 0)
{
return x_183;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_183, 0);
lean_inc(x_194);
lean_dec(x_183);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
block_233:
{
lean_object* x_218; lean_object* x_219; 
lean_inc_ref(x_215);
x_218 = l_Array_append___redArg(x_215, x_217);
lean_dec_ref(x_217);
lean_inc(x_205);
lean_inc(x_203);
x_219 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_219, 0, x_203);
lean_ctor_set(x_219, 1, x_205);
lean_ctor_set(x_219, 2, x_218);
if (lean_obj_tag(x_212) == 1)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_220 = lean_ctor_get(x_212, 0);
lean_inc(x_220);
lean_dec_ref(x_212);
x_221 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
x_222 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(x_203);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_203);
lean_ctor_set(x_223, 1, x_222);
x_224 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
lean_inc(x_203);
x_225 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_225, 0, x_203);
lean_ctor_set(x_225, 1, x_224);
x_226 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(x_203);
x_227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_227, 0, x_203);
lean_ctor_set(x_227, 1, x_226);
x_228 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(x_203);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_203);
lean_ctor_set(x_229, 1, x_228);
lean_inc(x_203);
x_230 = l_Lean_Syntax_node5(x_203, x_221, x_223, x_225, x_227, x_220, x_229);
x_231 = l_Array_mkArray1___redArg(x_230);
x_128 = x_197;
x_129 = x_198;
x_130 = x_199;
x_131 = x_200;
x_132 = x_201;
x_133 = x_202;
x_134 = x_203;
x_135 = x_204;
x_136 = x_205;
x_137 = x_206;
x_138 = x_207;
x_139 = x_209;
x_140 = x_208;
x_141 = x_210;
x_142 = x_211;
x_143 = x_219;
x_144 = x_214;
x_145 = lean_box(0);
x_146 = x_215;
x_147 = x_216;
x_148 = x_231;
goto block_196;
}
else
{
lean_object* x_232; 
lean_dec(x_212);
x_232 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
x_128 = x_197;
x_129 = x_198;
x_130 = x_199;
x_131 = x_200;
x_132 = x_201;
x_133 = x_202;
x_134 = x_203;
x_135 = x_204;
x_136 = x_205;
x_137 = x_206;
x_138 = x_207;
x_139 = x_209;
x_140 = x_208;
x_141 = x_210;
x_142 = x_211;
x_143 = x_219;
x_144 = x_214;
x_145 = lean_box(0);
x_146 = x_215;
x_147 = x_216;
x_148 = x_232;
goto block_196;
}
}
block_265:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_inc_ref(x_253);
x_255 = l_Array_append___redArg(x_253, x_254);
lean_dec_ref(x_254);
lean_inc(x_243);
lean_inc(x_241);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_241);
lean_ctor_set(x_256, 1, x_243);
lean_ctor_set(x_256, 2, x_255);
lean_inc(x_241);
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_241);
lean_ctor_set(x_257, 1, x_245);
if (lean_obj_tag(x_236) == 1)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = lean_ctor_get(x_236, 0);
lean_inc(x_258);
lean_dec_ref(x_236);
x_259 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
x_260 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(x_241);
x_261 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_261, 0, x_241);
lean_ctor_set(x_261, 1, x_260);
lean_inc(x_241);
x_262 = l_Lean_Syntax_node2(x_241, x_259, x_261, x_258);
x_263 = l_Array_mkArray1___redArg(x_262);
x_197 = x_234;
x_198 = x_235;
x_199 = x_237;
x_200 = x_238;
x_201 = x_239;
x_202 = x_240;
x_203 = x_241;
x_204 = x_242;
x_205 = x_243;
x_206 = x_244;
x_207 = x_256;
x_208 = x_247;
x_209 = x_246;
x_210 = x_248;
x_211 = x_249;
x_212 = x_252;
x_213 = lean_box(0);
x_214 = x_250;
x_215 = x_253;
x_216 = x_257;
x_217 = x_263;
goto block_233;
}
else
{
lean_object* x_264; 
lean_dec(x_236);
x_264 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
x_197 = x_234;
x_198 = x_235;
x_199 = x_237;
x_200 = x_238;
x_201 = x_239;
x_202 = x_240;
x_203 = x_241;
x_204 = x_242;
x_205 = x_243;
x_206 = x_244;
x_207 = x_256;
x_208 = x_247;
x_209 = x_246;
x_210 = x_248;
x_211 = x_249;
x_212 = x_252;
x_213 = lean_box(0);
x_214 = x_250;
x_215 = x_253;
x_216 = x_257;
x_217 = x_264;
goto block_233;
}
}
block_301:
{
lean_object* x_287; lean_object* x_288; 
lean_inc_ref(x_285);
x_287 = l_Array_append___redArg(x_285, x_286);
lean_dec_ref(x_286);
lean_inc(x_276);
lean_inc(x_274);
x_288 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_288, 0, x_274);
lean_ctor_set(x_288, 1, x_276);
lean_ctor_set(x_288, 2, x_287);
if (lean_obj_tag(x_267) == 1)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_289 = lean_ctor_get(x_267, 0);
lean_inc(x_289);
lean_dec_ref(x_267);
x_290 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(x_279);
x_291 = l_Lean_Name_mkStr4(x_27, x_28, x_279, x_290);
x_292 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(x_274);
x_293 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_293, 0, x_274);
lean_ctor_set(x_293, 1, x_292);
lean_inc_ref(x_285);
x_294 = l_Array_append___redArg(x_285, x_289);
lean_dec(x_289);
lean_inc(x_276);
lean_inc(x_274);
x_295 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_295, 0, x_274);
lean_ctor_set(x_295, 1, x_276);
lean_ctor_set(x_295, 2, x_294);
x_296 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(x_274);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_274);
lean_ctor_set(x_297, 1, x_296);
lean_inc(x_274);
x_298 = l_Lean_Syntax_node3(x_274, x_291, x_293, x_295, x_297);
x_299 = l_Array_mkArray1___redArg(x_298);
x_234 = x_266;
x_235 = x_268;
x_236 = x_269;
x_237 = x_270;
x_238 = x_271;
x_239 = x_272;
x_240 = x_273;
x_241 = x_274;
x_242 = x_275;
x_243 = x_276;
x_244 = x_288;
x_245 = x_277;
x_246 = x_279;
x_247 = x_278;
x_248 = x_280;
x_249 = x_281;
x_250 = x_284;
x_251 = lean_box(0);
x_252 = x_282;
x_253 = x_285;
x_254 = x_299;
goto block_265;
}
else
{
lean_object* x_300; 
lean_dec(x_267);
x_300 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
x_234 = x_266;
x_235 = x_268;
x_236 = x_269;
x_237 = x_270;
x_238 = x_271;
x_239 = x_272;
x_240 = x_273;
x_241 = x_274;
x_242 = x_275;
x_243 = x_276;
x_244 = x_288;
x_245 = x_277;
x_246 = x_279;
x_247 = x_278;
x_248 = x_280;
x_249 = x_281;
x_250 = x_284;
x_251 = lean_box(0);
x_252 = x_282;
x_253 = x_285;
x_254 = x_300;
goto block_265;
}
}
block_326:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
x_320 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__14));
x_321 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
x_322 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
if (lean_obj_tag(x_317) == 1)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_317, 0);
lean_inc(x_323);
lean_dec_ref(x_317);
x_324 = l_Array_mkArray1___redArg(x_323);
x_266 = x_302;
x_267 = x_303;
x_268 = x_304;
x_269 = x_305;
x_270 = x_306;
x_271 = x_307;
x_272 = x_308;
x_273 = x_320;
x_274 = x_309;
x_275 = x_310;
x_276 = x_321;
x_277 = x_319;
x_278 = x_311;
x_279 = x_312;
x_280 = x_313;
x_281 = x_314;
x_282 = x_316;
x_283 = lean_box(0);
x_284 = x_315;
x_285 = x_322;
x_286 = x_324;
goto block_301;
}
else
{
lean_object* x_325; 
lean_dec(x_317);
x_325 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
x_266 = x_302;
x_267 = x_303;
x_268 = x_304;
x_269 = x_305;
x_270 = x_306;
x_271 = x_307;
x_272 = x_308;
x_273 = x_320;
x_274 = x_309;
x_275 = x_310;
x_276 = x_321;
x_277 = x_319;
x_278 = x_311;
x_279 = x_312;
x_280 = x_313;
x_281 = x_314;
x_282 = x_316;
x_283 = lean_box(0);
x_284 = x_315;
x_285 = x_322;
x_286 = x_325;
goto block_301;
}
}
block_374:
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(x_337, 0, x_333);
lean_inc_ref(x_334);
x_338 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(x_337, x_334, x_335);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; size_t x_343; size_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = lean_unsigned_to_nat(7u);
x_341 = l_Lean_Syntax_getArg(x_1, x_340);
x_342 = l_Lean_Syntax_getArgs(x_341);
lean_dec(x_341);
x_343 = lean_array_size(x_342);
x_344 = 0;
x_345 = lean_box_usize(x_343);
x_346 = l_Lean_Elab_Command_elabNotation___boxed__const__1;
lean_inc_ref(x_342);
x_347 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(x_347, 0, x_345);
lean_closure_set(x_347, 1, x_346);
lean_closure_set(x_347, 2, x_342);
lean_inc_ref(x_334);
x_348 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(x_347, x_334, x_335);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = l_Lean_Elab_Command_getRef___redArg(x_334);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
x_352 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_334);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec_ref(x_352);
x_353 = lean_ctor_get(x_334, 5);
x_354 = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
x_355 = 0;
x_356 = l_Lean_mkIdentFrom(x_1, x_354, x_355);
x_357 = lean_unsigned_to_nat(9u);
x_358 = l_Lean_Syntax_getArg(x_1, x_357);
lean_dec(x_1);
lean_inc(x_358);
x_359 = l_Lean_Elab_Command_addInheritDocDefault(x_358, x_332);
x_360 = l_Lean_SourceInfo_fromRef(x_351, x_355);
lean_dec(x_351);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_361; 
x_361 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(x_335);
lean_dec_ref(x_361);
x_302 = x_358;
x_303 = x_359;
x_304 = x_342;
x_305 = x_329;
x_306 = x_335;
x_307 = x_344;
x_308 = x_339;
x_309 = x_360;
x_310 = x_349;
x_311 = x_356;
x_312 = x_327;
x_313 = x_334;
x_314 = x_328;
x_315 = x_355;
x_316 = x_330;
x_317 = x_331;
x_318 = lean_box(0);
goto block_326;
}
else
{
x_302 = x_358;
x_303 = x_359;
x_304 = x_342;
x_305 = x_329;
x_306 = x_335;
x_307 = x_344;
x_308 = x_339;
x_309 = x_360;
x_310 = x_349;
x_311 = x_356;
x_312 = x_327;
x_313 = x_334;
x_314 = x_328;
x_315 = x_355;
x_316 = x_330;
x_317 = x_331;
x_318 = lean_box(0);
goto block_326;
}
}
else
{
uint8_t x_362; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec_ref(x_342);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_1);
x_362 = !lean_is_exclusive(x_352);
if (x_362 == 0)
{
return x_352;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_352, 0);
lean_inc(x_363);
lean_dec(x_352);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_349);
lean_dec_ref(x_342);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_1);
x_365 = !lean_is_exclusive(x_350);
if (x_365 == 0)
{
return x_350;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_350, 0);
lean_inc(x_366);
lean_dec(x_350);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
return x_367;
}
}
}
else
{
uint8_t x_368; 
lean_dec_ref(x_342);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_1);
x_368 = !lean_is_exclusive(x_348);
if (x_368 == 0)
{
return x_348;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_348, 0);
lean_inc(x_369);
lean_dec(x_348);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_1);
x_371 = !lean_is_exclusive(x_338);
if (x_371 == 0)
{
return x_338;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_338, 0);
lean_inc(x_372);
lean_dec(x_338);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
return x_373;
}
}
}
block_398:
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_386 = lean_unsigned_to_nat(6u);
x_387 = l_Lean_Syntax_getArg(x_1, x_386);
x_388 = l_Lean_Syntax_isNone(x_387);
if (x_388 == 0)
{
uint8_t x_389; 
lean_inc(x_387);
x_389 = l_Lean_Syntax_matchesNull(x_387, x_375);
if (x_389 == 0)
{
lean_object* x_390; 
lean_dec(x_387);
lean_dec(x_384);
lean_dec_ref(x_383);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_379);
lean_dec(x_378);
lean_dec_ref(x_376);
lean_dec(x_1);
x_390 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_391 = l_Lean_Syntax_getArg(x_387, x_127);
lean_dec(x_387);
x_392 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(x_391);
x_393 = l_Lean_Syntax_isOfKind(x_391, x_392);
if (x_393 == 0)
{
lean_object* x_394; 
lean_dec(x_391);
lean_dec(x_384);
lean_dec_ref(x_383);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_379);
lean_dec(x_378);
lean_dec_ref(x_376);
lean_dec(x_1);
x_394 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = l_Lean_Syntax_getArg(x_391, x_377);
lean_dec(x_391);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
x_327 = x_376;
x_328 = x_379;
x_329 = x_378;
x_330 = x_382;
x_331 = x_380;
x_332 = x_381;
x_333 = x_396;
x_334 = x_383;
x_335 = x_384;
x_336 = lean_box(0);
goto block_374;
}
}
}
else
{
lean_object* x_397; 
lean_dec(x_387);
x_397 = lean_box(0);
x_327 = x_376;
x_328 = x_379;
x_329 = x_378;
x_330 = x_382;
x_331 = x_380;
x_332 = x_381;
x_333 = x_397;
x_334 = x_383;
x_335 = x_384;
x_336 = lean_box(0);
goto block_374;
}
}
block_421:
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_409 = lean_unsigned_to_nat(5u);
x_410 = l_Lean_Syntax_getArg(x_1, x_409);
x_411 = l_Lean_Syntax_isNone(x_410);
if (x_411 == 0)
{
uint8_t x_412; 
lean_inc(x_410);
x_412 = l_Lean_Syntax_matchesNull(x_410, x_399);
if (x_412 == 0)
{
lean_object* x_413; 
lean_dec(x_410);
lean_dec(x_407);
lean_dec_ref(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec_ref(x_400);
lean_dec(x_1);
x_413 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_414 = l_Lean_Syntax_getArg(x_410, x_127);
lean_dec(x_410);
x_415 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
lean_inc(x_414);
x_416 = l_Lean_Syntax_isOfKind(x_414, x_415);
if (x_416 == 0)
{
lean_object* x_417; 
lean_dec(x_414);
lean_dec(x_407);
lean_dec_ref(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec_ref(x_400);
lean_dec(x_1);
x_417 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = l_Lean_Syntax_getArg(x_414, x_401);
lean_dec(x_414);
x_419 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_419, 0, x_418);
x_375 = x_399;
x_376 = x_400;
x_377 = x_401;
x_378 = x_405;
x_379 = x_402;
x_380 = x_403;
x_381 = x_404;
x_382 = x_419;
x_383 = x_406;
x_384 = x_407;
x_385 = lean_box(0);
goto block_398;
}
}
}
else
{
lean_object* x_420; 
lean_dec(x_410);
x_420 = lean_box(0);
x_375 = x_399;
x_376 = x_400;
x_377 = x_401;
x_378 = x_405;
x_379 = x_402;
x_380 = x_403;
x_381 = x_404;
x_382 = x_420;
x_383 = x_406;
x_384 = x_407;
x_385 = lean_box(0);
goto block_398;
}
}
block_447:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_428 = lean_unsigned_to_nat(2u);
x_429 = l_Lean_Syntax_getArg(x_1, x_428);
x_430 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
x_431 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(x_429);
x_432 = l_Lean_Syntax_isOfKind(x_429, x_431);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec(x_429);
lean_dec(x_426);
lean_dec_ref(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_1);
x_433 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_434 = lean_unsigned_to_nat(3u);
x_435 = lean_unsigned_to_nat(4u);
x_436 = l_Lean_Syntax_getArg(x_1, x_435);
x_437 = l_Lean_Syntax_isNone(x_436);
if (x_437 == 0)
{
uint8_t x_438; 
lean_inc(x_436);
x_438 = l_Lean_Syntax_matchesNull(x_436, x_422);
if (x_438 == 0)
{
lean_object* x_439; 
lean_dec(x_436);
lean_dec(x_429);
lean_dec(x_426);
lean_dec_ref(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_1);
x_439 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_440 = l_Lean_Syntax_getArg(x_436, x_127);
lean_dec(x_436);
x_441 = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(x_440);
x_442 = l_Lean_Syntax_isOfKind(x_440, x_441);
if (x_442 == 0)
{
lean_object* x_443; 
lean_dec(x_440);
lean_dec(x_429);
lean_dec(x_426);
lean_dec_ref(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_1);
x_443 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = l_Lean_Syntax_getArg(x_440, x_422);
lean_dec(x_440);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_399 = x_422;
x_400 = x_430;
x_401 = x_434;
x_402 = x_429;
x_403 = x_423;
x_404 = x_424;
x_405 = x_445;
x_406 = x_425;
x_407 = x_426;
x_408 = lean_box(0);
goto block_421;
}
}
}
else
{
lean_object* x_446; 
lean_dec(x_436);
x_446 = lean_box(0);
x_399 = x_422;
x_400 = x_430;
x_401 = x_434;
x_402 = x_429;
x_403 = x_423;
x_404 = x_424;
x_405 = x_446;
x_406 = x_425;
x_407 = x_426;
x_408 = lean_box(0);
goto block_421;
}
}
}
block_465:
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_452 = lean_unsigned_to_nat(1u);
x_453 = l_Lean_Syntax_getArg(x_1, x_452);
x_454 = l_Lean_Syntax_isNone(x_453);
if (x_454 == 0)
{
uint8_t x_455; 
lean_inc(x_453);
x_455 = l_Lean_Syntax_matchesNull(x_453, x_452);
if (x_455 == 0)
{
lean_object* x_456; 
lean_dec(x_453);
lean_dec(x_450);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_1);
x_456 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_457 = l_Lean_Syntax_getArg(x_453, x_127);
lean_dec(x_453);
x_458 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(x_457);
x_459 = l_Lean_Syntax_isOfKind(x_457, x_458);
if (x_459 == 0)
{
lean_object* x_460; 
lean_dec(x_457);
lean_dec(x_450);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_1);
x_460 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = l_Lean_Syntax_getArg(x_457, x_452);
lean_dec(x_457);
x_462 = l_Lean_Syntax_getArgs(x_461);
lean_dec(x_461);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_422 = x_452;
x_423 = x_448;
x_424 = x_463;
x_425 = x_449;
x_426 = x_450;
x_427 = lean_box(0);
goto block_447;
}
}
}
else
{
lean_object* x_464; 
lean_dec(x_453);
x_464 = lean_box(0);
x_422 = x_452;
x_423 = x_448;
x_424 = x_464;
x_425 = x_449;
x_426 = x_450;
x_427 = lean_box(0);
goto block_447;
}
}
}
block_26:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander), 5, 3);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_inc_ref(x_8);
x_12 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(x_11, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Elab_Command_elabCommand(x_15, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Command_elabCommand(x_19, x_8, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
block_84:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_42 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
x_43 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc(x_31);
lean_inc(x_35);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_31);
lean_ctor_set(x_44, 2, x_40);
lean_inc(x_35);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_42);
x_46 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref(x_33);
x_47 = l_Lean_Name_mkStr4(x_27, x_28, x_33, x_46);
x_48 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
lean_inc_ref(x_33);
x_49 = l_Lean_Name_mkStr4(x_27, x_28, x_33, x_48);
x_50 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(x_35);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_50);
x_52 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
lean_inc_ref(x_33);
x_53 = l_Lean_Name_mkStr4(x_27, x_28, x_33, x_52);
x_54 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(x_35);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_35);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_35);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_37);
lean_inc_ref(x_56);
lean_inc(x_32);
lean_inc_ref(x_55);
lean_inc(x_53);
lean_inc(x_35);
x_57 = l_Lean_Syntax_node3(x_35, x_53, x_55, x_32, x_56);
lean_inc(x_31);
lean_inc(x_35);
x_58 = l_Lean_Syntax_node1(x_35, x_31, x_57);
lean_inc(x_31);
lean_inc(x_35);
x_59 = l_Lean_Syntax_node1(x_35, x_31, x_58);
x_60 = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(x_35);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_35);
lean_ctor_set(x_61, 1, x_60);
x_62 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
x_63 = l_Lean_Name_mkStr4(x_27, x_28, x_33, x_62);
x_64 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
lean_inc(x_35);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_35);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_36);
lean_inc(x_35);
x_66 = l_Lean_Syntax_node3(x_35, x_53, x_55, x_36, x_56);
lean_inc(x_35);
x_67 = l_Lean_Syntax_node2(x_35, x_63, x_65, x_66);
lean_inc(x_35);
x_68 = l_Lean_Syntax_node4(x_35, x_49, x_51, x_59, x_61, x_67);
lean_inc(x_35);
x_69 = l_Lean_Syntax_node1(x_35, x_31, x_68);
lean_inc(x_35);
x_70 = l_Lean_Syntax_node1(x_35, x_47, x_69);
lean_inc(x_39);
lean_inc_ref_n(x_44, 2);
x_71 = l_Lean_Syntax_node6(x_35, x_43, x_44, x_44, x_39, x_45, x_44, x_70);
lean_inc(x_39);
x_72 = l_Lean_Elab_Command_isLocalAttrKind(x_39);
if (x_72 == 0)
{
lean_object* x_73; 
lean_inc(x_38);
lean_inc_ref(x_34);
x_73 = l_Lean_Elab_Command_elabCommand(x_71, x_34, x_38);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_5 = x_32;
x_6 = x_36;
x_7 = x_39;
x_8 = x_34;
x_9 = x_38;
x_10 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_32);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_st_ref_get(x_38);
x_75 = lean_ctor_get(x_74, 2);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Elab_Command_instInhabitedScope_default;
x_77 = l_List_head_x21___redArg(x_76, x_75);
lean_dec(x_75);
x_78 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
x_80 = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(x_78, x_79, x_30);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(x_81, 0, x_80);
x_82 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_82, 0, x_71);
lean_inc(x_38);
lean_inc_ref(x_34);
x_83 = l_Lean_Elab_Command_withScope___redArg(x_81, x_82, x_34, x_38);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_5 = x_32;
x_6 = x_36;
x_7 = x_39;
x_8 = x_34;
x_9 = x_38;
x_10 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_32);
return x_83;
}
}
}
block_125:
{
size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_array_size(x_86);
x_101 = lean_box_usize(x_100);
x_102 = lean_box_usize(x_88);
x_103 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(x_103, 0, x_101);
lean_closure_set(x_103, 1, x_102);
lean_closure_set(x_103, 2, x_86);
lean_inc_ref(x_93);
x_104 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(x_103, x_93, x_89);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lean_Elab_Command_getRef___redArg(x_93);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_93);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_108);
x_109 = lean_ctor_get(x_93, 5);
x_110 = lean_array_size(x_99);
x_111 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(x_110, x_88, x_99);
x_112 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_111, x_85);
lean_dec_ref(x_111);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_87);
lean_ctor_set(x_113, 1, x_98);
lean_ctor_set(x_113, 2, x_105);
x_114 = l_Lean_SourceInfo_fromRef(x_107, x_96);
lean_dec(x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_115; 
x_115 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(x_89);
lean_dec_ref(x_115);
x_31 = x_90;
x_32 = x_113;
x_33 = x_92;
x_34 = x_93;
x_35 = x_114;
x_36 = x_112;
x_37 = x_94;
x_38 = x_89;
x_39 = x_95;
x_40 = x_97;
x_41 = lean_box(0);
goto block_84;
}
else
{
x_31 = x_90;
x_32 = x_113;
x_33 = x_92;
x_34 = x_93;
x_35 = x_114;
x_36 = x_112;
x_37 = x_94;
x_38 = x_89;
x_39 = x_95;
x_40 = x_97;
x_41 = lean_box(0);
goto block_84;
}
}
else
{
uint8_t x_116; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_85);
x_116 = !lean_is_exclusive(x_108);
if (x_116 == 0)
{
return x_108;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
lean_dec(x_108);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_105);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_85);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
return x_106;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_106, 0);
lean_inc(x_120);
lean_dec(x_106);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_85);
x_122 = !lean_is_exclusive(x_104);
if (x_122 == 0)
{
return x_104;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_104, 0);
lean_inc(x_123);
lean_dec(x_104);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabNotation(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7);
l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0 = _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
l_Lean_Elab_Command_mkUnexpander___closed__4 = _init_l_Lean_Elab_Command_mkUnexpander___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__4);
l_Lean_Elab_Command_mkUnexpander___closed__15 = _init_l_Lean_Elab_Command_mkUnexpander___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__15);
l_Lean_Elab_Command_mkUnexpander___closed__19 = _init_l_Lean_Elab_Command_mkUnexpander___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__19);
l_Lean_Elab_Command_mkUnexpander___closed__22 = _init_l_Lean_Elab_Command_mkUnexpander___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__22);
l_Lean_Elab_Command_mkUnexpander___closed__40 = _init_l_Lean_Elab_Command_mkUnexpander___closed__40();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__40);
l_Lean_Elab_Command_mkUnexpander___closed__47 = _init_l_Lean_Elab_Command_mkUnexpander___closed__47();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__47);
l_Lean_Elab_Command_mkUnexpander___closed__55 = _init_l_Lean_Elab_Command_mkUnexpander___closed__55();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__55);
l_Lean_Elab_Command_mkUnexpander___closed__68 = _init_l_Lean_Elab_Command_mkUnexpander___closed__68();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__68);
l_Lean_Elab_Command_mkUnexpander___closed__69 = _init_l_Lean_Elab_Command_mkUnexpander___closed__69();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__69);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3);
l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__6);
l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5);
l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0 = _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0();
l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1 = _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1);
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1();
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13);
l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2 = _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2();
lean_mark_persistent(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2);
l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3 = _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3();
lean_mark_persistent(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3);
l_Lean_Elab_Command_elabNotation___closed__9 = _init_l_Lean_Elab_Command_elabNotation___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabNotation___closed__9);
l_Lean_Elab_Command_elabNotation___boxed__const__1 = _init_l_Lean_Elab_Command_elabNotation___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Command_elabNotation___boxed__const__1);
if (builtin) {res = l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
