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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(lean_object* v_n_31_, uint8_t v___x_32_, uint8_t v___x_33_, lean_object* v_x_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_nat_dec_eq(v_x_34_, v_n_31_);
if (v___x_35_ == 0)
{
return v___x_32_;
}
else
{
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed(lean_object* v_n_36_, lean_object* v___x_37_, lean_object* v___x_38_, lean_object* v_x_39_){
_start:
{
uint8_t v___x_7745__boxed_40_; uint8_t v___x_7746__boxed_41_; uint8_t v_res_42_; lean_object* v_r_43_; 
v___x_7745__boxed_40_ = lean_unbox(v___x_37_);
v___x_7746__boxed_41_ = lean_unbox(v___x_38_);
v_res_42_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(v_n_36_, v___x_7745__boxed_40_, v___x_7746__boxed_41_, v_x_39_);
lean_dec(v_x_39_);
lean_dec(v_n_36_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(lean_object* v_n_44_, lean_object* v_x_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_lt(v_x_45_, v_n_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed(lean_object* v_n_47_, lean_object* v_x_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(v_n_47_, v_x_48_);
lean_dec(v_x_48_);
lean_dec(v_n_47_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(lean_object* v_n_51_, lean_object* v_x_52_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_nat_dec_le(v_x_52_, v_n_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed(lean_object* v_n_54_, lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(v_n_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec(v_n_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(lean_object* v_n_58_, lean_object* v_x_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lean_nat_dec_le(v_n_58_, v_x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed(lean_object* v_n_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(v_n_61_, v_x_62_);
lean_dec(v_x_62_);
lean_dec(v_n_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(lean_object* v_n_65_, lean_object* v_x_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_nat_dec_lt(v_n_65_, v_x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed(lean_object* v_n_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(v_n_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_n_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(lean_object* v_n_72_, lean_object* v_x_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_eq(v_x_73_, v_n_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed(lean_object* v_n_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(v_n_75_, v_x_76_);
lean_dec(v_x_76_);
lean_dec(v_n_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v_env_86_; lean_object* v___x_87_; lean_object* v_toCold_88_; lean_object* v_mctx_89_; lean_object* v_lctx_90_; lean_object* v_options_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_85_ = lean_st_ref_get(v___y_83_);
v_env_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_env_86_);
lean_dec(v___x_85_);
v___x_87_ = lean_st_ref_get(v___y_81_);
v_toCold_88_ = lean_ctor_get(v___y_82_, 0);
v_mctx_89_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_mctx_89_);
lean_dec(v___x_87_);
v_lctx_90_ = lean_ctor_get(v___y_80_, 2);
v_options_91_ = lean_ctor_get(v_toCold_88_, 2);
lean_inc_ref(v_options_91_);
lean_inc_ref(v_lctx_90_);
v___x_92_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_92_, 0, v_env_86_);
lean_ctor_set(v___x_92_, 1, v_mctx_89_);
lean_ctor_set(v___x_92_, 2, v_lctx_90_);
lean_ctor_set(v___x_92_, 3, v_options_91_);
v___x_93_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_msgData_79_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msgData_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(lean_object* v_msg_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_ref_108_; lean_object* v___x_109_; lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
v_ref_108_ = lean_ctor_get(v___y_105_, 2);
v___x_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msg_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_118_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_inc(v_ref_108_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_ref_108_);
lean_ctor_set(v___x_114_, 1, v_a_110_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 1);
lean_ctor_set(v___x_112_, 0, v___x_114_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg___boxed(lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(lean_object* v_ref_126_, lean_object* v_msg_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_toCold_137_; lean_object* v_currRecDepth_138_; lean_object* v_ref_139_; uint16_t v_optionFlags_140_; uint8_t v_suppressElabErrors_141_; uint8_t v_isRecordingDeps_142_; lean_object* v_ref_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_toCold_137_ = lean_ctor_get(v___y_134_, 0);
v_currRecDepth_138_ = lean_ctor_get(v___y_134_, 1);
v_ref_139_ = lean_ctor_get(v___y_134_, 2);
v_optionFlags_140_ = lean_ctor_get_uint16(v___y_134_, sizeof(void*)*3);
v_suppressElabErrors_141_ = lean_ctor_get_uint8(v___y_134_, sizeof(void*)*3 + 2);
v_isRecordingDeps_142_ = lean_ctor_get_uint8(v___y_134_, sizeof(void*)*3 + 3);
v_ref_143_ = l_Lean_replaceRef(v_ref_126_, v_ref_139_);
lean_inc(v_currRecDepth_138_);
lean_inc_ref(v_toCold_137_);
v___x_144_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_144_, 0, v_toCold_137_);
lean_ctor_set(v___x_144_, 1, v_currRecDepth_138_);
lean_ctor_set(v___x_144_, 2, v_ref_143_);
lean_ctor_set_uint16(v___x_144_, sizeof(void*)*3, v_optionFlags_140_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*3 + 2, v_suppressElabErrors_141_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*3 + 3, v_isRecordingDeps_142_);
v___x_145_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_127_, v___y_132_, v___y_133_, v___x_144_, v___y_135_);
lean_dec_ref_known(v___x_144_, 3);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg___boxed(lean_object* v_ref_146_, lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_146_, v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v_ref_146_);
return v_res_157_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(lean_object* v_filter_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5));
lean_inc(v_filter_263_);
v___x_274_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7));
lean_inc(v_filter_263_);
v___x_276_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9));
lean_inc(v_filter_263_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11));
lean_inc(v_filter_263_);
v___x_280_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13));
lean_inc(v_filter_263_);
v___x_282_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15));
lean_inc(v_filter_263_);
v___x_284_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17));
lean_inc(v_filter_263_);
v___x_286_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19));
lean_inc(v_filter_263_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21));
lean_inc(v_filter_263_);
v___x_290_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23));
lean_inc(v_filter_263_);
v___x_292_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25));
lean_inc(v_filter_263_);
v___x_294_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27));
lean_inc(v_filter_263_);
v___x_296_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29));
lean_inc(v_filter_263_);
v___x_298_ = l_Lean_Syntax_isOfKind(v_filter_263_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v_filter_263_);
v___x_299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v_n_301_; 
v___x_300_ = lean_unsigned_to_nat(2u);
v_n_301_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_300_);
lean_dec(v_filter_263_);
if (v___x_296_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_301_);
v___x_310_ = l_Lean_Syntax_isOfKind(v_n_301_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v_n_301_);
v___x_311_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_311_;
}
else
{
goto v___jp_302_;
}
}
else
{
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v_n_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_n_303_ = l_Lean_TSyntax_getNat(v_n_301_);
lean_dec(v_n_301_);
v___x_304_ = lean_box(v___x_298_);
v___x_305_ = lean_box(v___x_296_);
v___f_306_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed), 4, 3);
lean_closure_set(v___f_306_, 0, v_n_303_);
lean_closure_set(v___f_306_, 1, v___x_304_);
lean_closure_set(v___f_306_, 2, v___x_305_);
v___x_307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_307_, 0, v___f_306_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
}
else
{
lean_object* v___x_312_; lean_object* v_n_313_; 
v___x_312_ = lean_unsigned_to_nat(2u);
v_n_313_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_312_);
lean_dec(v_filter_263_);
if (v___x_294_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_313_);
v___x_320_ = l_Lean_Syntax_isOfKind(v_n_313_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
lean_dec(v_n_313_);
v___x_321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_321_;
}
else
{
goto v___jp_314_;
}
}
else
{
goto v___jp_314_;
}
v___jp_314_:
{
lean_object* v_n_315_; lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_n_315_ = l_Lean_TSyntax_getNat(v_n_313_);
lean_dec(v_n_313_);
v___f_316_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed), 2, 1);
lean_closure_set(v___f_316_, 0, v_n_315_);
v___x_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_317_, 0, v___f_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
}
else
{
lean_object* v___x_322_; lean_object* v_n_323_; 
v___x_322_ = lean_unsigned_to_nat(2u);
v_n_323_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_322_);
lean_dec(v_filter_263_);
if (v___x_292_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_323_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_n_323_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_n_323_);
v___x_331_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_331_;
}
else
{
goto v___jp_324_;
}
}
else
{
goto v___jp_324_;
}
v___jp_324_:
{
lean_object* v_n_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_n_325_ = l_Lean_TSyntax_getNat(v_n_323_);
lean_dec(v_n_323_);
v___f_326_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed), 2, 1);
lean_closure_set(v___f_326_, 0, v_n_325_);
v___x_327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_327_, 0, v___f_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
else
{
lean_object* v___x_332_; lean_object* v_n_333_; 
v___x_332_ = lean_unsigned_to_nat(2u);
v_n_333_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_332_);
lean_dec(v_filter_263_);
if (v___x_290_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_333_);
v___x_340_ = l_Lean_Syntax_isOfKind(v_n_333_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_n_333_);
v___x_341_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_341_;
}
else
{
goto v___jp_334_;
}
}
else
{
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v_n_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_n_335_ = l_Lean_TSyntax_getNat(v_n_333_);
lean_dec(v_n_333_);
v___f_336_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed), 2, 1);
lean_closure_set(v___f_336_, 0, v_n_335_);
v___x_337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_337_, 0, v___f_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v_n_343_; 
v___x_342_ = lean_unsigned_to_nat(2u);
v_n_343_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_342_);
lean_dec(v_filter_263_);
if (v___x_288_ == 0)
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_343_);
v___x_350_ = l_Lean_Syntax_isOfKind(v_n_343_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec(v_n_343_);
v___x_351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_351_;
}
else
{
goto v___jp_344_;
}
}
else
{
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v_n_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_n_345_ = l_Lean_TSyntax_getNat(v_n_343_);
lean_dec(v_n_343_);
v___f_346_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed), 2, 1);
lean_closure_set(v___f_346_, 0, v_n_345_);
v___x_347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_347_, 0, v___f_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
}
else
{
lean_object* v___x_352_; lean_object* v_n_353_; 
v___x_352_ = lean_unsigned_to_nat(2u);
v_n_353_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_352_);
lean_dec(v_filter_263_);
if (v___x_286_ == 0)
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_353_);
v___x_360_ = l_Lean_Syntax_isOfKind(v_n_353_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
lean_dec(v_n_353_);
v___x_361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_361_;
}
else
{
goto v___jp_354_;
}
}
else
{
goto v___jp_354_;
}
v___jp_354_:
{
lean_object* v_n_355_; lean_object* v___f_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_n_355_ = l_Lean_TSyntax_getNat(v_n_353_);
lean_dec(v_n_353_);
v___f_356_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed), 2, 1);
lean_closure_set(v___f_356_, 0, v_n_355_);
v___x_357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_357_, 0, v___f_356_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
else
{
lean_object* v___x_362_; lean_object* v_n_363_; 
v___x_362_ = lean_unsigned_to_nat(2u);
v_n_363_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_362_);
lean_dec(v_filter_263_);
if (v___x_284_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_363_);
v___x_370_ = l_Lean_Syntax_isOfKind(v_n_363_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_n_363_);
v___x_371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_371_;
}
else
{
goto v___jp_364_;
}
}
else
{
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v_n_365_; lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_n_365_ = l_Lean_TSyntax_getNat(v_n_363_);
lean_dec(v_n_363_);
v___f_366_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed), 2, 1);
lean_closure_set(v___f_366_, 0, v_n_365_);
v___x_367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_367_, 0, v___f_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
else
{
lean_object* v___x_372_; lean_object* v_n_373_; 
v___x_372_ = lean_unsigned_to_nat(2u);
v_n_373_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_372_);
lean_dec(v_filter_263_);
if (v___x_282_ == 0)
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_373_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_n_373_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_n_373_);
v___x_381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_381_;
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
v___jp_374_:
{
lean_object* v_n_375_; lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_n_375_ = l_Lean_TSyntax_getNat(v_n_373_);
lean_dec(v_n_373_);
v___f_376_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed), 2, 1);
lean_closure_set(v___f_376_, 0, v_n_375_);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v___f_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
}
else
{
lean_object* v___x_382_; lean_object* v_a_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v_a_383_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_382_);
lean_dec(v_filter_263_);
v_filter_263_ = v_a_383_;
goto _start;
}
}
else
{
lean_object* v___x_385_; lean_object* v_a_386_; lean_object* v___x_387_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v_a_386_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_385_);
lean_dec(v_filter_263_);
v___x_387_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_386_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_392_, 0, v_a_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
return v___x_387_;
}
}
}
else
{
lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v_b_400_; lean_object* v___x_401_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v_a_398_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_397_);
v___x_399_ = lean_unsigned_to_nat(2u);
v_b_400_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_399_);
lean_dec(v_filter_263_);
v___x_401_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_398_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_400_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v_a_402_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_dec(v_a_402_);
return v___x_403_;
}
}
else
{
lean_dec(v_b_400_);
return v___x_401_;
}
}
}
else
{
lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v_b_416_; lean_object* v___x_417_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v_a_414_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(2u);
v_b_416_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_415_);
lean_dec(v_filter_263_);
v___x_417_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_414_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
v___x_419_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_416_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_424_, 0, v_a_418_);
lean_ctor_set(v___x_424_, 1, v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
else
{
lean_dec(v_a_418_);
return v___x_419_;
}
}
else
{
lean_dec(v_b_416_);
return v___x_417_;
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Lean_Syntax_getArg(v_filter_263_, v___x_429_);
lean_dec(v_filter_263_);
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35));
lean_inc(v___x_430_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_430_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v___x_430_);
v___x_444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_444_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36));
v___x_446_ = 0;
lean_inc(v___x_430_);
v___x_447_ = l_Lean_Elab_Term_resolveId_x3f(v___x_430_, v___x_445_, v___x_446_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_471_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_471_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_471_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_471_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
if (lean_obj_tag(v_a_448_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_470_; 
v_val_452_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_470_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_470_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_470_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
switch(lean_obj_tag(v_val_452_))
{
case 4:
{
lean_object* v_declName_456_; lean_object* v___x_458_; 
lean_dec(v___x_430_);
v_declName_456_ = lean_ctor_get(v_val_452_, 0);
lean_inc(v_declName_456_);
lean_dec_ref_known(v_val_452_, 2);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_declName_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_declName_456_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_458_);
v___x_460_ = v___x_450_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
case 1:
{
lean_object* v_fvarId_463_; lean_object* v___x_465_; 
lean_dec(v___x_430_);
v_fvarId_463_ = lean_ctor_get(v_val_452_, 0);
lean_inc(v_fvarId_463_);
lean_dec_ref_known(v_val_452_, 1);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 2);
lean_ctor_set(v___x_454_, 0, v_fvarId_463_);
v___x_465_ = v___x_454_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fvarId_463_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_465_);
v___x_467_ = v___x_450_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
default: 
{
lean_del_object(v___x_454_);
lean_dec(v_val_452_);
lean_del_object(v___x_450_);
v___y_432_ = v_a_264_;
v___y_433_ = v_a_265_;
v___y_434_ = v_a_266_;
v___y_435_ = v_a_267_;
v___y_436_ = v_a_268_;
v___y_437_ = v_a_269_;
v___y_438_ = v_a_270_;
v___y_439_ = v_a_271_;
goto v___jp_431_;
}
}
}
}
else
{
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
v___y_432_ = v_a_264_;
v___y_433_ = v_a_265_;
v___y_434_ = v_a_266_;
v___y_435_ = v_a_267_;
v___y_436_ = v_a_268_;
v___y_437_ = v_a_269_;
v___y_438_ = v_a_270_;
v___y_439_ = v_a_271_;
goto v___jp_431_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v___x_430_);
v_a_472_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_447_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_447_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
v___jp_431_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33, &l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_once, _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33);
v___x_441_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v___x_430_, v___x_440_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___x_430_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___boxed(lean_object* v_filter_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_filter_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(lean_object* v_00_u03b1_491_, lean_object* v_ref_492_, lean_object* v_msg_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_492_, v_msg_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___boxed(lean_object* v_00_u03b1_504_, lean_object* v_ref_505_, lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(v_00_u03b1_504_, v_ref_505_, v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v_ref_505_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(lean_object* v_00_u03b1_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_518_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_529_, lean_object* v_msg_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(v_00_u03b1_529_, v_msg_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter(lean_object* v_filter_x3f_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
if (lean_obj_tag(v_filter_x3f_541_) == 1)
{
lean_object* v_val_551_; lean_object* v___x_552_; 
v_val_551_ = lean_ctor_get(v_filter_x3f_541_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_filter_x3f_541_, 1);
v___x_552_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_val_551_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_filter_x3f_541_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter___boxed(lean_object* v_filter_x3f_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_565_;
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
