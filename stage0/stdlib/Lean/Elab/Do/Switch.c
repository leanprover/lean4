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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabNestedAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLiftMethod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "legacy"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(51, 126, 45, 195, 115, 115, 51, 135)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 232, 139, 88, 91, 137, 183, 76)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "Use the legacy `do` elaborator instead of the new, extensible implementation."};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 119, 213, 61, 119, 26, 225, 248)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 69, 170, 166, 145, 126, 34, 117)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(116, 140, 133, 118, 51, 249, 1, 254)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_backward_do_legacy;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Term_expandTermFor___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termFor"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 224, 91, 133, 33, 161, 189, 246)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandTermFor"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 67, 19, 221, 19, 241, 218, 200)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__1_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1805) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Term_expandTermTry___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termTry"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 80, 182, 167, 150, 154, 214, 88)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandTermTry"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 94, 241, 17, 100, 182, 152, 84)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__1_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1808) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermUnless___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termUnless"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 93, 2, 77, 146, 4, 53, 233)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandTermUnless"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 215, 22, 211, 57, 247, 242, 171)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__1_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1811) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandTermReturn"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 153, 4, 104, 223, 208, 206, 177)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__1_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1814) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "elabDo"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 179, 33, 138, 106, 169, 223, 171)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabTermLiftMethod"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 231, 120, 173, 186, 18, 41, 72)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_();
return v_res_63_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Array_mkArray0(lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(lean_object* v_newKind_86_, lean_object* v_stx_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_ref_90_; lean_object* v_stx_91_; lean_object* v_ref_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_ref_90_ = lean_ctor_get(v_a_88_, 5);
v_stx_91_ = l_Lean_Syntax_setKind(v_stx_87_, v_newKind_86_);
v_ref_92_ = l_Lean_replaceRef(v_stx_91_, v_ref_90_);
v___x_93_ = 0;
v___x_94_ = l_Lean_SourceInfo_fromRef(v_ref_92_, v___x_93_);
lean_dec(v_ref_92_);
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_));
v___x_96_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1));
lean_inc_n(v___x_94_, 5);
v___x_97_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_94_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
v___x_98_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3));
v___x_99_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5));
v___x_100_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7));
v___x_101_ = lean_obj_once(&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8, &l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once, _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8);
v___x_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_94_);
lean_ctor_set(v___x_102_, 1, v___x_99_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
v___x_103_ = l_Lean_Syntax_node2(v___x_94_, v___x_100_, v_stx_91_, v___x_102_);
v___x_104_ = l_Lean_Syntax_node1(v___x_94_, v___x_99_, v___x_103_);
v___x_105_ = l_Lean_Syntax_node1(v___x_94_, v___x_98_, v___x_104_);
v___x_106_ = l_Lean_Syntax_node2(v___x_94_, v___x_96_, v___x_97_, v___x_105_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_89_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(lean_object* v_newKind_108_, lean_object* v_stx_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v_newKind_108_, v_stx_109_, v_a_110_, v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor(lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___closed__1));
v___x_123_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_122_, v_a_119_, v_a_120_, v_a_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___boxed(lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Elab_Term_expandTermFor(v_a_124_, v_a_125_, v_a_126_);
lean_dec_ref(v_a_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1(){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_141_ = l_Lean_Elab_macroAttribute;
v___x_142_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1));
v___x_143_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3));
v___x_144_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermFor___boxed), 3, 0);
v___x_145_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_141_, v___x_142_, v___x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___boxed(lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3(){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3));
v___x_175_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6));
v___x_176_ = l_Lean_addBuiltinDeclarationRanges(v___x_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___boxed(lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry(lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Elab_Term_expandTermTry___closed__1));
v___x_189_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_188_, v_a_185_, v_a_186_, v_a_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___boxed(lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Elab_Term_expandTermTry(v_a_190_, v_a_191_, v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1(){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = l_Lean_Elab_macroAttribute;
v___x_208_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1));
v___x_209_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3));
v___x_210_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermTry___boxed), 3, 0);
v___x_211_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_207_, v___x_208_, v___x_209_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___boxed(lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3));
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6));
v___x_242_ = l_Lean_addBuiltinDeclarationRanges(v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___boxed(lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless(lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___closed__1));
v___x_255_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_254_, v_a_251_, v_a_252_, v_a_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___boxed(lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Term_expandTermUnless(v_a_256_, v_a_257_, v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1(){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = l_Lean_Elab_macroAttribute;
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1));
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3));
v___x_276_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermUnless___boxed), 3, 0);
v___x_277_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_273_, v___x_274_, v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___boxed(lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3(){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3));
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6));
v___x_308_ = l_Lean_addBuiltinDeclarationRanges(v___x_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___boxed(lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn(lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___closed__1));
v___x_321_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_320_, v_a_317_, v_a_318_, v_a_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___boxed(lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Elab_Term_expandTermReturn(v_a_322_, v_a_323_, v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1(){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_339_ = l_Lean_Elab_macroAttribute;
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1));
v___x_341_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3));
v___x_342_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermReturn___boxed), 3, 0);
v___x_343_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_339_, v___x_340_, v___x_341_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___boxed(lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3(){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3));
v___x_373_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6));
v___x_374_ = l_Lean_addBuiltinDeclarationRanges(v___x_372_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___boxed(lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(lean_object* v_opts_377_, lean_object* v_opt_378_){
_start:
{
lean_object* v_name_379_; lean_object* v_defValue_380_; lean_object* v_map_381_; lean_object* v___x_382_; 
v_name_379_ = lean_ctor_get(v_opt_378_, 0);
v_defValue_380_ = lean_ctor_get(v_opt_378_, 1);
v_map_381_ = lean_ctor_get(v_opts_377_, 0);
v___x_382_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_381_, v_name_379_);
if (lean_obj_tag(v___x_382_) == 0)
{
uint8_t v___x_383_; 
v___x_383_ = lean_unbox(v_defValue_380_);
return v___x_383_;
}
else
{
lean_object* v_val_384_; 
v_val_384_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_384_);
lean_dec_ref(v___x_382_);
if (lean_obj_tag(v_val_384_) == 1)
{
uint8_t v_v_385_; 
v_v_385_ = lean_ctor_get_uint8(v_val_384_, 0);
lean_dec_ref(v_val_384_);
return v_v_385_;
}
else
{
uint8_t v___x_386_; 
lean_dec(v_val_384_);
v___x_386_ = lean_unbox(v_defValue_380_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0___boxed(lean_object* v_opts_387_, lean_object* v_opt_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_opts_387_, v_opt_388_);
lean_dec_ref(v_opt_388_);
lean_dec_ref(v_opts_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo(lean_object* v_stx_391_, lean_object* v_expectedType_x3f_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_options_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_options_400_ = lean_ctor_get(v_a_397_, 2);
v___x_401_ = l_Lean_Elab_Term_backward_do_legacy;
v___x_402_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_options_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Do_elabDo(v_stx_391_, v_expectedType_x3f_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Elab_Term_Do_elabDo(v_stx_391_, v_expectedType_x3f_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___boxed(lean_object* v_stx_405_, lean_object* v_expectedType_x3f_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_Term_elabDo(v_stx_405_, v_expectedType_x3f_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1(){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_422_ = l_Lean_Elab_Term_termElabAttribute;
v___x_423_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1));
v___x_424_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1));
v___x_425_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo___boxed), 9, 0);
v___x_426_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_422_, v___x_423_, v___x_424_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg(lean_object* v_stx_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_options_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_options_437_ = lean_ctor_get(v_a_434_, 2);
v___x_438_ = l_Lean_Elab_Term_backward_do_legacy;
v___x_439_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_options_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Elab_Do_elabNestedAction___redArg(v_stx_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Elab_Term_elabLiftMethod___redArg(v_stx_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_stx_429_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___redArg___boxed(lean_object* v_stx_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Elab_Term_elabTermLiftMethod___redArg(v_stx_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod(lean_object* v_stx_451_, lean_object* v_ty_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Elab_Term_elabTermLiftMethod___redArg(v_stx_451_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermLiftMethod___boxed(lean_object* v_stx_461_, lean_object* v_ty_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Elab_Term_elabTermLiftMethod(v_stx_461_, v_ty_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_ty_462_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1(){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = l_Lean_Elab_Term_termElabAttribute;
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__1));
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___closed__3));
v___x_487_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermLiftMethod___boxed), 9, 0);
v___x_488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_484_, v___x_485_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1___boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1();
return v_res_490_;
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
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_2514403911____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_backward_do_legacy = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_backward_do_legacy);
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermLiftMethod___regBuiltin_Lean_Elab_Term_elabTermLiftMethod__1();
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
