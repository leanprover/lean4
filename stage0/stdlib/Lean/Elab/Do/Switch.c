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
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabNestedAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNestedAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "legacy"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(51, 126, 45, 195, 115, 115, 51, 135)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 232, 139, 88, 91, 137, 183, 76)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "Use the legacy `do` elaborator instead of the new, extensible implementation."};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__4_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__0_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 119, 213, 61, 119, 26, 225, 248)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 69, 170, 166, 145, 126, 34, 117)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__2_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(116, 140, 133, 118, 51, 249, 1, 254)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_backward_do_legacy;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandTermFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Term_expandTermFor___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Term_expandTermFor___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termFor"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 224, 91, 133, 33, 161, 189, 246)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandTermFor"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
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
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Term_expandTermTry___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termTry"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 80, 182, 167, 150, 154, 214, 88)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandTermTry"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
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
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermUnless___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Term_expandTermUnless___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermUnless___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termUnless"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 93, 2, 77, 146, 4, 53, 233)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandTermUnless"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
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
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandTermReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Term_expandTermReturn___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandTermReturn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandTermReturn"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
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
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 179, 33, 138, 106, 169, 223, 171)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermNestedAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermNestedAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermNestedAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermNestedAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 27, 24, 243, 204, 49, 153, 202)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "elabTermNestedAction"};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__6_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__7_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__8_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(10, 212, 28, 198, 91, 183, 85, 112)}};
static const lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___boxed(lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__3_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__5_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__9_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_));
v___x_62_ = l_Lean_Option_register___at___00__private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__spec__0(v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_63_;
v_res_63_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_();
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_();
return v_res_65_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Array_mkArray0___redArg();
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(lean_object* v_newKind_88_, lean_object* v_stx_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_ref_92_; lean_object* v_stx_93_; lean_object* v_ref_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_ref_92_ = lean_ctor_get(v_a_90_, 5);
v_stx_93_ = l_Lean_Syntax_setKind(v_stx_89_, v_newKind_88_);
v_ref_94_ = l_Lean_replaceRef(v_stx_93_, v_ref_92_);
v___x_95_ = 0;
v___x_96_ = l_Lean_SourceInfo_fromRef(v_ref_94_, v___x_95_);
lean_dec(v_ref_94_);
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn___closed__1_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_));
v___x_98_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1));
lean_inc_n(v___x_96_, 5);
v___x_99_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_96_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
v___x_100_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__3));
v___x_101_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__5));
v___x_102_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__7));
v___x_103_ = lean_obj_once(&l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8, &l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8_once, _init_l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__8);
v___x_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_96_);
lean_ctor_set(v___x_104_, 1, v___x_101_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
v___x_105_ = l_Lean_Syntax_node2(v___x_96_, v___x_102_, v_stx_93_, v___x_104_);
v___x_106_ = l_Lean_Syntax_node1(v___x_96_, v___x_101_, v___x_105_);
v___x_107_ = l_Lean_Syntax_node1(v___x_96_, v___x_100_, v___x_106_);
v___x_108_ = l_Lean_Syntax_node2(v___x_96_, v___x_98_, v___x_99_, v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_91_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___boxed(lean_object* v_newKind_110_, lean_object* v_stx_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v_newKind_110_, v_stx_111_, v_a_112_, v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor(lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Term_expandTermFor___closed__1));
v___x_125_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_124_, v_a_121_, v_a_122_, v_a_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermFor___boxed(lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Elab_Term_expandTermFor(v_a_126_, v_a_127_, v_a_128_);
lean_dec_ref(v_a_127_);
return v_res_129_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1(){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = l_Lean_Elab_macroAttribute;
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__1));
v___x_145_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3));
v___x_146_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermFor___boxed), 3, 0);
v___x_147_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_143_, v___x_144_, v___x_145_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_148_;
v_res_148_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1();
return v_res_150_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3(){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor__1___closed__3));
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___closed__6));
v___x_179_ = l_Lean_addBuiltinDeclarationRanges(v___x_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_180_;
v_res_180_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3___boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermFor___regBuiltin_Lean_Elab_Term_expandTermFor_declRange__3();
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
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1(){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_211_ = l_Lean_Elab_macroAttribute;
v___x_212_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__1));
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3));
v___x_214_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermTry___boxed), 3, 0);
v___x_215_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_211_, v___x_212_, v___x_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_216_;
v_res_216_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___boxed(lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1();
return v_res_218_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3(){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry__1___closed__3));
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___closed__6));
v___x_247_ = l_Lean_addBuiltinDeclarationRanges(v___x_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_248_;
v_res_248_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermTry___regBuiltin_Lean_Elab_Term_expandTermTry_declRange__3();
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless(lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Elab_Term_expandTermUnless___closed__1));
v___x_261_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_260_, v_a_257_, v_a_258_, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermUnless___boxed(lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Elab_Term_expandTermUnless(v_a_262_, v_a_263_, v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_265_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1(){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_279_ = l_Lean_Elab_macroAttribute;
v___x_280_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__1));
v___x_281_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3));
v___x_282_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermUnless___boxed), 3, 0);
v___x_283_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_279_, v___x_280_, v___x_281_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_284_;
v_res_284_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___boxed(lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1();
return v_res_286_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3(){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless__1___closed__3));
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___closed__6));
v___x_315_ = l_Lean_addBuiltinDeclarationRanges(v___x_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_316_;
v_res_316_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3___boxed(lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermUnless___regBuiltin_Lean_Elab_Term_expandTermUnless_declRange__3();
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn(lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_Term_expandTermReturn___closed__1));
v___x_329_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem(v___x_328_, v_a_325_, v_a_326_, v_a_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTermReturn___boxed(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_Term_expandTermReturn(v_a_330_, v_a_331_, v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_333_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_347_ = l_Lean_Elab_macroAttribute;
v___x_348_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__1));
v___x_349_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3));
v___x_350_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTermReturn___boxed), 3, 0);
v___x_351_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_347_, v___x_348_, v___x_349_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_352_;
v_res_352_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___boxed(lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1();
return v_res_354_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3(){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn__1___closed__3));
v___x_382_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___closed__6));
v___x_383_ = l_Lean_addBuiltinDeclarationRanges(v___x_381_, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_384_;
v_res_384_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3___boxed(lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_expandTermReturn___regBuiltin_Lean_Elab_Term_expandTermReturn_declRange__3();
return v_res_386_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(lean_object* v_opts_387_, lean_object* v_opt_388_){
_start:
{
lean_object* v_name_389_; lean_object* v_defValue_390_; lean_object* v_map_391_; lean_object* v___x_392_; 
v_name_389_ = lean_ctor_get(v_opt_388_, 0);
v_defValue_390_ = lean_ctor_get(v_opt_388_, 1);
v_map_391_ = lean_ctor_get(v_opts_387_, 0);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_391_, v_name_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
uint8_t v___x_393_; 
v___x_393_ = lean_unbox(v_defValue_390_);
return v___x_393_;
}
else
{
lean_object* v_val_394_; 
v_val_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_392_, 1);
if (lean_obj_tag(v_val_394_) == 1)
{
uint8_t v_v_395_; 
v_v_395_ = lean_ctor_get_uint8(v_val_394_, 0);
lean_dec_ref_known(v_val_394_, 0);
return v_v_395_;
}
else
{
uint8_t v___x_396_; 
lean_dec(v_val_394_);
v___x_396_ = lean_unbox(v_defValue_390_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_387_ = stack[0].m_obj;
lean_object* v_opt_388_ = stack[1].m_obj;
uint8_t v_res_397_;
v_res_397_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_opts_387_, v_opt_388_);
stack->m_num = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0___boxed(lean_object* v_opts_398_, lean_object* v_opt_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v_opts_398_, v_opt_399_);
lean_dec_ref(v_opt_399_);
lean_dec_ref(v_opts_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
lean_object* l_Lean_Elab_Term_elabDo(lean_object* v_stx_402_, lean_object* v_expectedType_x3f_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_411_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_408_);
v___x_412_ = l_Lean_Elab_Term_backward_do_legacy;
v___x_413_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v___x_411_, v___x_412_);
lean_dec_ref(v___x_411_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_Do_elabDo(v_stx_402_, v_expectedType_x3f_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Elab_Term_Do_elabDo(v_stx_402_, v_expectedType_x3f_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_415_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabDo_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_402_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_403_ = stack[1].m_obj;
lean_object* v_a_404_ = stack[2].m_obj;
lean_object* v_a_405_ = stack[3].m_obj;
lean_object* v_a_406_ = stack[4].m_obj;
lean_object* v_a_407_ = stack[5].m_obj;
lean_object* v_a_408_ = stack[6].m_obj;
lean_object* v_a_409_ = stack[7].m_obj;
lean_object* v_res_416_;
v_res_416_ = l_Lean_Elab_Term_elabDo(v_stx_402_, v_expectedType_x3f_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDo___boxed(lean_object* v_stx_417_, lean_object* v_expectedType_x3f_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_Term_elabDo(v_stx_417_, v_expectedType_x3f_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_426_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1(){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = l_Lean_Elab_Term_termElabAttribute;
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_toDoElem___closed__1));
v___x_436_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___closed__1));
v___x_437_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo___boxed), 9, 0);
v___x_438_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_434_, v___x_435_, v___x_436_, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_439_;
v_res_439_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1___boxed(lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabDo___regBuiltin_Lean_Elab_Term_elabDo__1();
return v_res_441_;
}
}
lean_object* l_Lean_Elab_Term_elabTermNestedAction___redArg(lean_object* v_stx_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_447_);
v___x_451_ = l_Lean_Elab_Term_backward_do_legacy;
v___x_452_ = l_Lean_Option_get___at___00Lean_Elab_Term_elabDo_spec__0(v___x_450_, v___x_451_);
lean_dec_ref(v___x_450_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Elab_Do_elabNestedAction___redArg(v_stx_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Elab_Term_elabNestedAction___redArg(v_stx_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_stx_442_);
return v___x_454_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabTermNestedAction___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_442_ = stack[0].m_obj;
lean_object* v_a_443_ = stack[1].m_obj;
lean_object* v_a_444_ = stack[2].m_obj;
lean_object* v_a_445_ = stack[3].m_obj;
lean_object* v_a_446_ = stack[4].m_obj;
lean_object* v_a_447_ = stack[5].m_obj;
lean_object* v_a_448_ = stack[6].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_Elab_Term_elabTermNestedAction___redArg(v_stx_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermNestedAction___redArg___boxed(lean_object* v_stx_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Elab_Term_elabTermNestedAction___redArg(v_stx_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_464_;
}
}
lean_object* l_Lean_Elab_Term_elabTermNestedAction(lean_object* v_stx_465_, lean_object* v_ty_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Elab_Term_elabTermNestedAction___redArg(v_stx_465_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
return v___x_474_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabTermNestedAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_465_ = stack[0].m_obj;
lean_object* v_ty_466_ = stack[1].m_obj;
lean_object* v_a_467_ = stack[2].m_obj;
lean_object* v_a_468_ = stack[3].m_obj;
lean_object* v_a_469_ = stack[4].m_obj;
lean_object* v_a_470_ = stack[5].m_obj;
lean_object* v_a_471_ = stack[6].m_obj;
lean_object* v_a_472_ = stack[7].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lean_Elab_Term_elabTermNestedAction(v_stx_465_, v_ty_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermNestedAction___boxed(lean_object* v_stx_476_, lean_object* v_ty_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Elab_Term_elabTermNestedAction(v_stx_476_, v_ty_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_ty_477_);
return v_res_485_;
}
}
lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1(){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_499_ = l_Lean_Elab_Term_termElabAttribute;
v___x_500_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__1));
v___x_501_ = ((lean_object*)(l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___closed__3));
v___x_502_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermNestedAction___boxed), 9, 0);
v___x_503_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_499_, v___x_500_, v___x_501_, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_504_;
v_res_504_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1();
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1___boxed(lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1();
return v_res_506_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Legacy(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_Switch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Do_Switch_1835640568____hygCtx___hyg_4_();
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
res = l___private_Lean_Elab_Do_Switch_0__Lean_Elab_Term_elabTermNestedAction___regBuiltin_Lean_Elab_Term_elabTermNestedAction__1();
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
