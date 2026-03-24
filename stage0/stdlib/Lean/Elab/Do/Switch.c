// Lean compiler output
// Module: Lean.Elab.Do.Switch
// Imports: public import Lean.Elab.Term.TermElabM import Lean.Elab.Do.Basic import Lean.Elab.Do.Legacy
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
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabNestedAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLiftMethod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "legacy"};
static const lean_object* l_Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(51, 126, 45, 195, 115, 115, 51, 135)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 232, 139, 88, 91, 137, 183, 76)}};
static const lean_object* l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "Use the legacy `do` elaborator instead of the new, extensible implementation."};
static const lean_object* l_Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 119, 213, 61, 119, 26, 225, 248)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 69, 170, 166, 145, 126, 34, 117)}};
static const lean_ctor_object l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(116, 140, 133, 118, 51, 249, 1, 254)}};
static const lean_object* l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_backward_do_legacy;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Term_expandTermFor___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termFor"};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 224, 91, 133, 33, 161, 189, 246)}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandTermFor"};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 67, 19, 221, 19, 241, 218, 200)}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Term_expandTermTry___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termTry"};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 80, 182, 167, 150, 154, 214, 88)}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandTermTry"};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 94, 241, 17, 100, 182, 152, 84)}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermUnless___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termUnless"};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 93, 2, 77, 146, 4, 53, 233)}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandTermUnless"};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 215, 22, 211, 57, 247, 242, 171)}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandTermReturn"};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 153, 4, 104, 223, 208, 206, 177)}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "elabDo"};
static const lean_object* l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 179, 33, 138, 106, 169, 223, 171)}};
static const lean_object* l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabTermLiftMethod"};
static const lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 231, 120, 173, 186, 18, 41, 72)}};
static const lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l_Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_63_ = ((lean_object*)(l_Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_64_ = ((lean_object*)(l_Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_65_ = l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_();
return v_res_67_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Array_mkArray0(lean_box(0));
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(lean_object* v_newKind_90_, lean_object* v_stx_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_ref_94_; lean_object* v_stx_95_; lean_object* v_ref_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_ref_94_ = lean_ctor_get(v_a_92_, 5);
v_stx_95_ = l_Lean_Syntax_setKind(v_stx_91_, v_newKind_90_);
v_ref_96_ = l_Lean_replaceRef(v_stx_95_, v_ref_94_);
v___x_97_ = 0;
v___x_98_ = l_Lean_SourceInfo_fromRef(v_ref_96_, v___x_97_);
lean_dec(v_ref_96_);
v___x_99_ = ((lean_object*)(l_Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_100_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1));
lean_inc(v___x_98_);
v___x_101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_98_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
v___x_102_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3));
v___x_103_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5));
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7));
v___x_105_ = lean_obj_once(&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8, &l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once, _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8);
lean_inc(v___x_98_);
v___x_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_98_);
lean_ctor_set(v___x_106_, 1, v___x_103_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
lean_inc(v___x_98_);
v___x_107_ = l_Lean_Syntax_node2(v___x_98_, v___x_104_, v_stx_95_, v___x_106_);
lean_inc(v___x_98_);
v___x_108_ = l_Lean_Syntax_node1(v___x_98_, v___x_103_, v___x_107_);
lean_inc(v___x_98_);
v___x_109_ = l_Lean_Syntax_node1(v___x_98_, v___x_102_, v___x_108_);
v___x_110_ = l_Lean_Syntax_node2(v___x_98_, v___x_100_, v___x_101_, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_93_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(lean_object* v_newKind_112_, lean_object* v_stx_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v_newKind_112_, v_stx_113_, v_a_114_, v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor(lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___closed__1));
v___x_127_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_126_, v_a_123_, v_a_124_, v_a_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___boxed(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Elab_Term_expandTermFor(v_a_128_, v_a_129_, v_a_130_);
lean_dec_ref(v_a_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1(){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_145_ = l_Lean_Elab_macroAttribute;
v___x_146_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1));
v___x_147_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3));
v___x_148_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermFor___boxed), 3, 0);
v___x_149_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_145_, v___x_146_, v___x_147_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___boxed(lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3(){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3));
v___x_179_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6));
v___x_180_ = l_Lean_addBuiltinDeclarationRanges(v___x_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry(lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_Term_expandTermTry___closed__1));
v___x_193_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_192_, v_a_189_, v_a_190_, v_a_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___boxed(lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Term_expandTermTry(v_a_194_, v_a_195_, v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1(){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_211_ = l_Lean_Elab_macroAttribute;
v___x_212_ = ((lean_object*)(l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1));
v___x_213_ = ((lean_object*)(l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3));
v___x_214_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermTry___boxed), 3, 0);
v___x_215_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_211_, v___x_212_, v___x_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___boxed(lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3(){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3));
v___x_245_ = ((lean_object*)(l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6));
v___x_246_ = l_Lean_addBuiltinDeclarationRanges(v___x_244_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___boxed(lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless(lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___closed__1));
v___x_259_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_258_, v_a_255_, v_a_256_, v_a_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___boxed(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Elab_Term_expandTermUnless(v_a_260_, v_a_261_, v_a_262_);
lean_dec_ref(v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1(){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_277_ = l_Lean_Elab_macroAttribute;
v___x_278_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1));
v___x_279_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3));
v___x_280_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermUnless___boxed), 3, 0);
v___x_281_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_277_, v___x_278_, v___x_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3(){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3));
v___x_311_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6));
v___x_312_ = l_Lean_addBuiltinDeclarationRanges(v___x_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___boxed(lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn(lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___closed__1));
v___x_325_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_324_, v_a_321_, v_a_322_, v_a_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___boxed(lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Elab_Term_expandTermReturn(v_a_326_, v_a_327_, v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1(){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_343_ = l_Lean_Elab_macroAttribute;
v___x_344_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1));
v___x_345_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3));
v___x_346_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermReturn___boxed), 3, 0);
v___x_347_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_343_, v___x_344_, v___x_345_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___boxed(lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3(){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3));
v___x_377_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6));
v___x_378_ = l_Lean_addBuiltinDeclarationRanges(v___x_376_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___boxed(lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(lean_object* v_opts_381_, lean_object* v_opt_382_){
_start:
{
lean_object* v_name_383_; lean_object* v_defValue_384_; lean_object* v_map_385_; lean_object* v___x_386_; 
v_name_383_ = lean_ctor_get(v_opt_382_, 0);
v_defValue_384_ = lean_ctor_get(v_opt_382_, 1);
v_map_385_ = lean_ctor_get(v_opts_381_, 0);
v___x_386_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_385_, v_name_383_);
if (lean_obj_tag(v___x_386_) == 0)
{
uint8_t v___x_387_; 
v___x_387_ = lean_unbox(v_defValue_384_);
return v___x_387_;
}
else
{
lean_object* v_val_388_; 
v_val_388_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_388_);
lean_dec_ref(v___x_386_);
if (lean_obj_tag(v_val_388_) == 1)
{
uint8_t v_v_389_; 
v_v_389_ = lean_ctor_get_uint8(v_val_388_, 0);
lean_dec_ref(v_val_388_);
return v_v_389_;
}
else
{
uint8_t v___x_390_; 
lean_dec(v_val_388_);
v___x_390_ = lean_unbox(v_defValue_384_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0___boxed(lean_object* v_opts_391_, lean_object* v_opt_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_opts_391_, v_opt_392_);
lean_dec_ref(v_opt_392_);
lean_dec_ref(v_opts_391_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo(lean_object* v_stx_395_, lean_object* v_expectedType_x3f_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_options_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_options_404_ = lean_ctor_get(v_a_401_, 2);
v___x_405_ = l_Lean_Elab_Term_backward_do_legacy;
v___x_406_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_options_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Elab_Do_elabDo(v_stx_395_, v_expectedType_x3f_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Elab_Term_Do_elabDo(v_stx_395_, v_expectedType_x3f_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___boxed(lean_object* v_stx_409_, lean_object* v_expectedType_x3f_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_Term_elabDo(v_stx_409_, v_expectedType_x3f_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = l_Lean_Elab_Term_termElabAttribute;
v___x_427_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1));
v___x_428_ = ((lean_object*)(l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1));
v___x_429_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo___boxed), 9, 0);
v___x_430_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_426_, v___x_427_, v___x_428_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg(lean_object* v_stx_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_options_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_options_441_ = lean_ctor_get(v_a_438_, 2);
v___x_442_ = l_Lean_Elab_Term_backward_do_legacy;
v___x_443_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_options_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Elab_Do_elabNestedAction___redArg(v_stx_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Elab_Term_elabLiftMethod___redArg(v_stx_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_stx_433_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg___boxed(lean_object* v_stx_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_Term_elabTermLiftMethod___redArg(v_stx_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod(lean_object* v_stx_455_, lean_object* v_ty_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Elab_Term_elabTermLiftMethod___redArg(v_stx_455_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___boxed(lean_object* v_stx_465_, lean_object* v_ty_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_Term_elabTermLiftMethod(v_stx_465_, v_ty_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_ty_466_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1(){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_488_ = l_Lean_Elab_Term_termElabAttribute;
v___x_489_ = ((lean_object*)(l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1));
v___x_490_ = ((lean_object*)(l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3));
v___x_491_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermLiftMethod___boxed), 9, 0);
v___x_492_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_488_, v___x_489_, v___x_490_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___boxed(lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1();
return v_res_494_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Legacy(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_Switch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_backward_do_legacy = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_backward_do_legacy);
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_Switch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Legacy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_Switch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Switch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_Switch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_Switch(builtin);
}
#ifdef __cplusplus
}
#endif
