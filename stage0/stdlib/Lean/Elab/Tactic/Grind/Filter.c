// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Filter
// Imports: public import Lean.Elab.Tactic.Grind.Basic public import Lean.Meta.Tactic.Grind.Filter
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grind_filter_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(42, 183, 54, 132, 193, 221, 83, 246)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grind_filter_&&_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 18, 222, 93, 166, 92, 88, 35)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grind_filter_||_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(172, 127, 248, 101, 151, 207, 64, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_filter!_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(191, 240, 71, 91, 236, 83, 171, 27)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grind_filter(_)"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(118, 150, 229, 147, 17, 198, 129, 17)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen=_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(46, 110, 208, 13, 150, 123, 60, 151)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen>_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(139, 245, 163, 142, 72, 168, 216, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = "grind_filterGen≥_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(67, 138, 8, 224, 7, 211, 129, 34)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen>=_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(197, 129, 153, 143, 173, 111, 170, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = "grind_filterGen≤_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(160, 191, 11, 181, 243, 245, 215, 191)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen<=_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(126, 96, 49, 75, 137, 142, 109, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen<_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(86, 91, 104, 32, 61, 131, 243, 196)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen!=_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28_value),LEAN_SCALAR_PTR_LITERAL(58, 149, 94, 94, 69, 234, 169, 170)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid identifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v___y_18_ = stack[8].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_32_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(lean_object* v_n_33_, uint8_t v___x_34_, uint8_t v___x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_nat_dec_eq(v_x_36_, v_n_33_);
if (v___x_37_ == 0)
{
return v___x_34_;
}
else
{
return v___x_35_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_33_ = stack[0].m_obj;
uint8_t v___x_34_ = stack[1].m_num;
uint8_t v___x_35_ = stack[2].m_num;
lean_object* v_x_36_ = stack[3].m_obj;
uint8_t v_res_38_;
v_res_38_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(v_n_33_, v___x_34_, v___x_35_, v_x_36_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed(lean_object* v_n_39_, lean_object* v___x_40_, lean_object* v___x_41_, lean_object* v_x_42_){
_start:
{
uint8_t v___x_7777__boxed_43_; uint8_t v___x_7778__boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v___x_7777__boxed_43_ = lean_unbox(v___x_40_);
v___x_7778__boxed_44_ = lean_unbox(v___x_41_);
v_res_45_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(v_n_39_, v___x_7777__boxed_43_, v___x_7778__boxed_44_, v_x_42_);
lean_dec(v_x_42_);
lean_dec(v_n_39_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(lean_object* v_n_47_, lean_object* v_x_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_lt(v_x_48_, v_n_47_);
return v___x_49_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_47_ = stack[0].m_obj;
lean_object* v_x_48_ = stack[1].m_obj;
uint8_t v_res_50_;
v_res_50_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(v_n_47_, v_x_48_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed(lean_object* v_n_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(v_n_51_, v_x_52_);
lean_dec(v_x_52_);
lean_dec(v_n_51_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(lean_object* v_n_55_, lean_object* v_x_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_le(v_x_56_, v_n_55_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_55_ = stack[0].m_obj;
lean_object* v_x_56_ = stack[1].m_obj;
uint8_t v_res_58_;
v_res_58_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(v_n_55_, v_x_56_);
stack->m_num = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed(lean_object* v_n_59_, lean_object* v_x_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(v_n_59_, v_x_60_);
lean_dec(v_x_60_);
lean_dec(v_n_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(lean_object* v_n_63_, lean_object* v_x_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_le(v_n_63_, v_x_64_);
return v___x_65_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_63_ = stack[0].m_obj;
lean_object* v_x_64_ = stack[1].m_obj;
uint8_t v_res_66_;
v_res_66_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(v_n_63_, v_x_64_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed(lean_object* v_n_67_, lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(v_n_67_, v_x_68_);
lean_dec(v_x_68_);
lean_dec(v_n_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(lean_object* v_n_71_, lean_object* v_x_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_nat_dec_lt(v_n_71_, v_x_72_);
return v___x_73_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_71_ = stack[0].m_obj;
lean_object* v_x_72_ = stack[1].m_obj;
uint8_t v_res_74_;
v_res_74_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(v_n_71_, v_x_72_);
stack->m_num = v_res_74_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed(lean_object* v_n_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(v_n_75_, v_x_76_);
lean_dec(v_x_76_);
lean_dec(v_n_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(lean_object* v_n_79_, lean_object* v_x_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_nat_dec_eq(v_x_80_, v_n_79_);
return v___x_81_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_79_ = stack[0].m_obj;
lean_object* v_x_80_ = stack[1].m_obj;
uint8_t v_res_82_;
v_res_82_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(v_n_79_, v_x_80_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed(lean_object* v_n_83_, lean_object* v_x_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(v_n_83_, v_x_84_);
lean_dec(v_x_84_);
lean_dec(v_n_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(lean_object* v_msgData_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_env_94_; uint8_t v___x_95_; lean_object* v_env_96_; lean_object* v___x_97_; lean_object* v_toCold_98_; lean_object* v_mctx_99_; lean_object* v_lctx_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = 0;
v_env_96_ = l_Lean_Environment_setRecordingDeps(v_env_94_, v___x_95_);
v___x_97_ = lean_st_ref_get(v___y_89_);
v_toCold_98_ = lean_ctor_get(v___y_90_, 0);
v_mctx_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_mctx_99_);
lean_dec(v___x_97_);
v_lctx_100_ = lean_ctor_get(v___y_88_, 2);
v_options_101_ = lean_ctor_get(v_toCold_98_, 2);
lean_inc_ref(v_options_101_);
lean_inc_ref(v_lctx_100_);
v___x_102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_102_, 0, v_env_96_);
lean_ctor_set(v___x_102_, 1, v_mctx_99_);
lean_ctor_set(v___x_102_, 2, v_lctx_100_);
lean_ctor_set(v___x_102_, 3, v_options_101_);
v___x_103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_msgData_87_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_87_ = stack[0].m_obj;
lean_object* v___y_88_ = stack[1].m_obj;
lean_object* v___y_89_ = stack[2].m_obj;
lean_object* v___y_90_ = stack[3].m_obj;
lean_object* v___y_91_ = stack[4].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msgData_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_119_ = lean_ctor_get(v___y_116_, 2);
v___x_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_119_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_113_ = stack[0].m_obj;
lean_object* v___y_114_ = stack[1].m_obj;
lean_object* v___y_115_ = stack[2].m_obj;
lean_object* v___y_116_ = stack[3].m_obj;
lean_object* v___y_117_ = stack[4].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg___boxed(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_137_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(lean_object* v_ref_138_, lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_toCold_149_; lean_object* v_currRecDepth_150_; lean_object* v_ref_151_; uint16_t v_optionFlags_152_; uint8_t v_suppressElabErrors_153_; uint8_t v_isRecordingDeps_154_; lean_object* v_ref_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_toCold_149_ = lean_ctor_get(v___y_146_, 0);
v_currRecDepth_150_ = lean_ctor_get(v___y_146_, 1);
v_ref_151_ = lean_ctor_get(v___y_146_, 2);
v_optionFlags_152_ = lean_ctor_get_uint16(v___y_146_, sizeof(void*)*3);
v_suppressElabErrors_153_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 2);
v_isRecordingDeps_154_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 3);
v_ref_155_ = l_Lean_replaceRef(v_ref_138_, v_ref_151_);
lean_inc(v_currRecDepth_150_);
lean_inc_ref(v_toCold_149_);
v___x_156_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_156_, 0, v_toCold_149_);
lean_ctor_set(v___x_156_, 1, v_currRecDepth_150_);
lean_ctor_set(v___x_156_, 2, v_ref_155_);
lean_ctor_set_uint16(v___x_156_, sizeof(void*)*3, v_optionFlags_152_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*3 + 2, v_suppressElabErrors_153_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*3 + 3, v_isRecordingDeps_154_);
v___x_157_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_139_, v___y_144_, v___y_145_, v___x_156_, v___y_147_);
lean_dec_ref_known(v___x_156_, 3);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_138_ = stack[0].m_obj;
lean_object* v_msg_139_ = stack[1].m_obj;
lean_object* v___y_140_ = stack[2].m_obj;
lean_object* v___y_141_ = stack[3].m_obj;
lean_object* v___y_142_ = stack[4].m_obj;
lean_object* v___y_143_ = stack[5].m_obj;
lean_object* v___y_144_ = stack[6].m_obj;
lean_object* v___y_145_ = stack[7].m_obj;
lean_object* v___y_146_ = stack[8].m_obj;
lean_object* v___y_147_ = stack[9].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_138_, v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg___boxed(lean_object* v_ref_159_, lean_object* v_msg_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_159_, v_msg_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_ref_159_);
return v_res_170_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(lean_object* v_filter_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5));
lean_inc(v_filter_276_);
v___x_287_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7));
lean_inc(v_filter_276_);
v___x_289_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9));
lean_inc(v_filter_276_);
v___x_291_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11));
lean_inc(v_filter_276_);
v___x_293_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13));
lean_inc(v_filter_276_);
v___x_295_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15));
lean_inc(v_filter_276_);
v___x_297_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17));
lean_inc(v_filter_276_);
v___x_299_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19));
lean_inc(v_filter_276_);
v___x_301_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21));
lean_inc(v_filter_276_);
v___x_303_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23));
lean_inc(v_filter_276_);
v___x_305_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25));
lean_inc(v_filter_276_);
v___x_307_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27));
lean_inc(v_filter_276_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29));
lean_inc(v_filter_276_);
v___x_311_ = l_Lean_Syntax_isOfKind(v_filter_276_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec(v_filter_276_);
v___x_312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v_n_314_; 
v___x_313_ = lean_unsigned_to_nat(2u);
v_n_314_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_313_);
lean_dec(v_filter_276_);
if (v___x_309_ == 0)
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_314_);
v___x_323_ = l_Lean_Syntax_isOfKind(v_n_314_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_n_314_);
v___x_324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_324_;
}
else
{
goto v___jp_315_;
}
}
else
{
goto v___jp_315_;
}
v___jp_315_:
{
lean_object* v_n_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_n_316_ = l_Lean_TSyntax_getNat(v_n_314_);
lean_dec(v_n_314_);
v___x_317_ = lean_box(v___x_311_);
v___x_318_ = lean_box(v___x_309_);
v___f_319_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed), 4, 3);
lean_closure_set(v___f_319_, 0, v_n_316_);
lean_closure_set(v___f_319_, 1, v___x_317_);
lean_closure_set(v___f_319_, 2, v___x_318_);
v___x_320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_320_, 0, v___f_319_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v_n_326_; 
v___x_325_ = lean_unsigned_to_nat(2u);
v_n_326_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_325_);
lean_dec(v_filter_276_);
if (v___x_307_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_326_);
v___x_333_ = l_Lean_Syntax_isOfKind(v_n_326_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_n_326_);
v___x_334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_334_;
}
else
{
goto v___jp_327_;
}
}
else
{
goto v___jp_327_;
}
v___jp_327_:
{
lean_object* v_n_328_; lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_n_328_ = l_Lean_TSyntax_getNat(v_n_326_);
lean_dec(v_n_326_);
v___f_329_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed), 2, 1);
lean_closure_set(v___f_329_, 0, v_n_328_);
v___x_330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_330_, 0, v___f_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v_n_336_; 
v___x_335_ = lean_unsigned_to_nat(2u);
v_n_336_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_335_);
lean_dec(v_filter_276_);
if (v___x_305_ == 0)
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_336_);
v___x_343_ = l_Lean_Syntax_isOfKind(v_n_336_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_n_336_);
v___x_344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_344_;
}
else
{
goto v___jp_337_;
}
}
else
{
goto v___jp_337_;
}
v___jp_337_:
{
lean_object* v_n_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_n_338_ = l_Lean_TSyntax_getNat(v_n_336_);
lean_dec(v_n_336_);
v___f_339_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed), 2, 1);
lean_closure_set(v___f_339_, 0, v_n_338_);
v___x_340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_340_, 0, v___f_339_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
else
{
lean_object* v___x_345_; lean_object* v_n_346_; 
v___x_345_ = lean_unsigned_to_nat(2u);
v_n_346_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_345_);
lean_dec(v_filter_276_);
if (v___x_303_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_346_);
v___x_353_ = l_Lean_Syntax_isOfKind(v_n_346_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec(v_n_346_);
v___x_354_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_354_;
}
else
{
goto v___jp_347_;
}
}
else
{
goto v___jp_347_;
}
v___jp_347_:
{
lean_object* v_n_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_n_348_ = l_Lean_TSyntax_getNat(v_n_346_);
lean_dec(v_n_346_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed), 2, 1);
lean_closure_set(v___f_349_, 0, v_n_348_);
v___x_350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_350_, 0, v___f_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
else
{
lean_object* v___x_355_; lean_object* v_n_356_; 
v___x_355_ = lean_unsigned_to_nat(2u);
v_n_356_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_355_);
lean_dec(v_filter_276_);
if (v___x_301_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_356_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_n_356_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec(v_n_356_);
v___x_364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_364_;
}
else
{
goto v___jp_357_;
}
}
else
{
goto v___jp_357_;
}
v___jp_357_:
{
lean_object* v_n_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_n_358_ = l_Lean_TSyntax_getNat(v_n_356_);
lean_dec(v_n_356_);
v___f_359_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed), 2, 1);
lean_closure_set(v___f_359_, 0, v_n_358_);
v___x_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_360_, 0, v___f_359_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
else
{
lean_object* v___x_365_; lean_object* v_n_366_; 
v___x_365_ = lean_unsigned_to_nat(2u);
v_n_366_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_365_);
lean_dec(v_filter_276_);
if (v___x_299_ == 0)
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_366_);
v___x_373_ = l_Lean_Syntax_isOfKind(v_n_366_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_n_366_);
v___x_374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_374_;
}
else
{
goto v___jp_367_;
}
}
else
{
goto v___jp_367_;
}
v___jp_367_:
{
lean_object* v_n_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_n_368_ = l_Lean_TSyntax_getNat(v_n_366_);
lean_dec(v_n_366_);
v___f_369_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed), 2, 1);
lean_closure_set(v___f_369_, 0, v_n_368_);
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v___f_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
else
{
lean_object* v___x_375_; lean_object* v_n_376_; 
v___x_375_ = lean_unsigned_to_nat(2u);
v_n_376_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_375_);
lean_dec(v_filter_276_);
if (v___x_297_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_376_);
v___x_383_ = l_Lean_Syntax_isOfKind(v_n_376_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec(v_n_376_);
v___x_384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_384_;
}
else
{
goto v___jp_377_;
}
}
else
{
goto v___jp_377_;
}
v___jp_377_:
{
lean_object* v_n_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_n_378_ = l_Lean_TSyntax_getNat(v_n_376_);
lean_dec(v_n_376_);
v___f_379_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed), 2, 1);
lean_closure_set(v___f_379_, 0, v_n_378_);
v___x_380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_380_, 0, v___f_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
else
{
lean_object* v___x_385_; lean_object* v_n_386_; 
v___x_385_ = lean_unsigned_to_nat(2u);
v_n_386_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_385_);
lean_dec(v_filter_276_);
if (v___x_295_ == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_386_);
v___x_393_ = l_Lean_Syntax_isOfKind(v_n_386_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec(v_n_386_);
v___x_394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_394_;
}
else
{
goto v___jp_387_;
}
}
else
{
goto v___jp_387_;
}
v___jp_387_:
{
lean_object* v_n_388_; lean_object* v___f_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_n_388_ = l_Lean_TSyntax_getNat(v_n_386_);
lean_dec(v_n_386_);
v___f_389_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed), 2, 1);
lean_closure_set(v___f_389_, 0, v_n_388_);
v___x_390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_390_, 0, v___f_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
}
else
{
lean_object* v___x_395_; lean_object* v_a_396_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v_a_396_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_395_);
lean_dec(v_filter_276_);
v_filter_276_ = v_a_396_;
goto _start;
}
}
else
{
lean_object* v___x_398_; lean_object* v_a_399_; lean_object* v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v_a_399_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_398_);
lean_dec(v_filter_276_);
v___x_400_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_399_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_405_, 0, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
return v___x_400_;
}
}
}
else
{
lean_object* v___x_410_; lean_object* v_a_411_; lean_object* v___x_412_; lean_object* v_b_413_; lean_object* v___x_414_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v_a_411_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_410_);
v___x_412_ = lean_unsigned_to_nat(2u);
v_b_413_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_412_);
lean_dec(v_filter_276_);
v___x_414_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_411_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_413_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_425_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_421_, 0, v_a_415_);
lean_ctor_set(v___x_421_, 1, v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_dec(v_a_415_);
return v___x_416_;
}
}
else
{
lean_dec(v_b_413_);
return v___x_414_;
}
}
}
else
{
lean_object* v___x_426_; lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v_b_429_; lean_object* v___x_430_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v_a_427_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_426_);
v___x_428_ = lean_unsigned_to_nat(2u);
v_b_429_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_428_);
lean_dec(v_filter_276_);
v___x_430_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_427_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v___x_432_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_429_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_441_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v_a_431_);
lean_ctor_set(v___x_437_, 1, v_a_433_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_dec(v_a_431_);
return v___x_432_;
}
}
else
{
lean_dec(v_b_429_);
return v___x_430_;
}
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = l_Lean_Syntax_getArg(v_filter_276_, v___x_442_);
lean_dec(v_filter_276_);
v___x_455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35));
lean_inc(v___x_443_);
v___x_456_ = l_Lean_Syntax_isOfKind(v___x_443_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v___x_443_);
v___x_457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_457_;
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36));
v___x_459_ = 0;
lean_inc(v___x_443_);
v___x_460_ = l_Lean_Elab_Term_resolveId_x3f(v___x_443_, v___x_458_, v___x_459_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_484_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_484_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_484_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_484_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
if (lean_obj_tag(v_a_461_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_483_; 
v_val_465_ = lean_ctor_get(v_a_461_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_461_);
if (v_isSharedCheck_483_ == 0)
{
v___x_467_ = v_a_461_;
v_isShared_468_ = v_isSharedCheck_483_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_val_465_);
lean_dec(v_a_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_483_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
switch(lean_obj_tag(v_val_465_))
{
case 4:
{
lean_object* v_declName_469_; lean_object* v___x_471_; 
lean_dec(v___x_443_);
v_declName_469_ = lean_ctor_get(v_val_465_, 0);
lean_inc(v_declName_469_);
lean_dec_ref_known(v_val_465_, 2);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v_declName_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_declName_469_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_471_);
v___x_473_ = v___x_463_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
case 1:
{
lean_object* v_fvarId_476_; lean_object* v___x_478_; 
lean_dec(v___x_443_);
v_fvarId_476_ = lean_ctor_get(v_val_465_, 0);
lean_inc(v_fvarId_476_);
lean_dec_ref_known(v_val_465_, 1);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 2);
lean_ctor_set(v___x_467_, 0, v_fvarId_476_);
v___x_478_ = v___x_467_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fvarId_476_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_478_);
v___x_480_ = v___x_463_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
default: 
{
lean_del_object(v___x_467_);
lean_dec(v_val_465_);
lean_del_object(v___x_463_);
v___y_445_ = v_a_277_;
v___y_446_ = v_a_278_;
v___y_447_ = v_a_279_;
v___y_448_ = v_a_280_;
v___y_449_ = v_a_281_;
v___y_450_ = v_a_282_;
v___y_451_ = v_a_283_;
v___y_452_ = v_a_284_;
goto v___jp_444_;
}
}
}
}
else
{
lean_del_object(v___x_463_);
lean_dec(v_a_461_);
v___y_445_ = v_a_277_;
v___y_446_ = v_a_278_;
v___y_447_ = v_a_279_;
v___y_448_ = v_a_280_;
v___y_449_ = v_a_281_;
v___y_450_ = v_a_282_;
v___y_451_ = v_a_283_;
v___y_452_ = v_a_284_;
goto v___jp_444_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v___x_443_);
v_a_485_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_460_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_460_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
v___jp_444_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33, &l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_once, _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33);
v___x_454_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v___x_443_, v___x_453_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___x_443_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_276_ = stack[0].m_obj;
lean_object* v_a_277_ = stack[1].m_obj;
lean_object* v_a_278_ = stack[2].m_obj;
lean_object* v_a_279_ = stack[3].m_obj;
lean_object* v_a_280_ = stack[4].m_obj;
lean_object* v_a_281_ = stack[5].m_obj;
lean_object* v_a_282_ = stack[6].m_obj;
lean_object* v_a_283_ = stack[7].m_obj;
lean_object* v_a_284_ = stack[8].m_obj;
lean_object* v_res_493_;
v_res_493_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_filter_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___boxed(lean_object* v_filter_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_filter_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_504_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(lean_object* v_00_u03b1_505_, lean_object* v_ref_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_506_, v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
return v___x_517_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_506_ = stack[1].m_obj;
lean_object* v_msg_507_ = stack[2].m_obj;
lean_object* v___y_508_ = stack[3].m_obj;
lean_object* v___y_509_ = stack[4].m_obj;
lean_object* v___y_510_ = stack[5].m_obj;
lean_object* v___y_511_ = stack[6].m_obj;
lean_object* v___y_512_ = stack[7].m_obj;
lean_object* v___y_513_ = stack[8].m_obj;
lean_object* v___y_514_ = stack[9].m_obj;
lean_object* v___y_515_ = stack[10].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(lean_box(0), v_ref_506_, v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___boxed(lean_object* v_00_u03b1_519_, lean_object* v_ref_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(v_00_u03b1_519_, v_ref_520_, v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v_ref_520_);
return v_res_531_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(lean_object* v_00_u03b1_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_533_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
return v___x_543_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_533_ = stack[1].m_obj;
lean_object* v___y_534_ = stack[2].m_obj;
lean_object* v___y_535_ = stack[3].m_obj;
lean_object* v___y_536_ = stack[4].m_obj;
lean_object* v___y_537_ = stack[5].m_obj;
lean_object* v___y_538_ = stack[6].m_obj;
lean_object* v___y_539_ = stack[7].m_obj;
lean_object* v___y_540_ = stack[8].m_obj;
lean_object* v___y_541_ = stack[9].m_obj;
lean_object* v_res_544_;
v_res_544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(lean_box(0), v_msg_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
stack->m_obj
 = v_res_544_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(v_00_u03b1_545_, v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_556_;
}
}
lean_object* l_Lean_Elab_Tactic_Grind_elabFilter(lean_object* v_filter_x3f_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
if (lean_obj_tag(v_filter_x3f_557_) == 1)
{
lean_object* v_val_567_; lean_object* v___x_568_; 
v_val_567_ = lean_ctor_get(v_filter_x3f_557_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_filter_x3f_557_, 1);
v___x_568_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_val_567_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_filter_x3f_557_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Grind_elabFilter_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_x3f_557_ = stack[0].m_obj;
lean_object* v_a_558_ = stack[1].m_obj;
lean_object* v_a_559_ = stack[2].m_obj;
lean_object* v_a_560_ = stack[3].m_obj;
lean_object* v_a_561_ = stack[4].m_obj;
lean_object* v_a_562_ = stack[5].m_obj;
lean_object* v_a_563_ = stack[6].m_obj;
lean_object* v_a_564_ = stack[7].m_obj;
lean_object* v_a_565_ = stack[8].m_obj;
lean_object* v_res_571_;
v_res_571_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter___boxed(lean_object* v_filter_x3f_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_582_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
}
#ifdef __cplusplus
}
#endif
