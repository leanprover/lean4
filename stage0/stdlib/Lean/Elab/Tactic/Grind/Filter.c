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
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid identifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36;
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(lean_object* v_n_31_, lean_object* v_x_32_){
_start:
{
uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = lean_nat_dec_eq(v_x_32_, v_n_31_);
v___x_34_ = lean_bool_not(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed(lean_object* v_n_35_, lean_object* v_x_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(v_n_35_, v_x_36_);
lean_dec(v_x_36_);
lean_dec(v_n_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(lean_object* v_n_39_, lean_object* v_x_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = lean_nat_dec_lt(v_x_40_, v_n_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed(lean_object* v_n_42_, lean_object* v_x_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(v_n_42_, v_x_43_);
lean_dec(v_x_43_);
lean_dec(v_n_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(lean_object* v_n_46_, lean_object* v_x_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_nat_dec_le(v_x_47_, v_n_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed(lean_object* v_n_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(v_n_49_, v_x_50_);
lean_dec(v_x_50_);
lean_dec(v_n_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(lean_object* v_n_53_, lean_object* v_x_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_nat_dec_le(v_n_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed(lean_object* v_n_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(v_n_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_n_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(lean_object* v_n_60_, lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = lean_nat_dec_lt(v_n_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed(lean_object* v_n_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(v_n_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_n_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(lean_object* v_n_67_, lean_object* v_x_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_eq(v_x_68_, v_n_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed(lean_object* v_n_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(v_n_70_, v_x_71_);
lean_dec(v_x_71_);
lean_dec(v_n_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(lean_object* v_msgData_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; lean_object* v_env_81_; lean_object* v___x_82_; lean_object* v_mctx_83_; lean_object* v_lctx_84_; lean_object* v_options_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_80_ = lean_st_ref_get(v___y_78_);
v_env_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc_ref(v_env_81_);
lean_dec(v___x_80_);
v___x_82_ = lean_st_ref_get(v___y_76_);
v_mctx_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_mctx_83_);
lean_dec(v___x_82_);
v_lctx_84_ = lean_ctor_get(v___y_75_, 2);
v_options_85_ = lean_ctor_get(v___y_77_, 2);
lean_inc_ref(v_options_85_);
lean_inc_ref(v_lctx_84_);
v___x_86_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_86_, 0, v_env_81_);
lean_ctor_set(v___x_86_, 1, v_mctx_83_);
lean_ctor_set(v___x_86_, 2, v_lctx_84_);
lean_ctor_set(v___x_86_, 3, v_options_85_);
v___x_87_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_msgData_74_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msgData_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_ref_102_; lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_112_; 
v_ref_102_ = lean_ctor_get(v___y_99_, 5);
v___x_103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msg_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_112_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_110_; 
lean_inc(v_ref_102_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_ref_102_);
lean_ctor_set(v___x_108_, 1, v_a_104_);
if (v_isShared_107_ == 0)
{
lean_ctor_set_tag(v___x_106_, 1);
lean_ctor_set(v___x_106_, 0, v___x_108_);
v___x_110_ = v___x_106_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg___boxed(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(lean_object* v_ref_120_, lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_fileName_131_; lean_object* v_fileMap_132_; lean_object* v_options_133_; lean_object* v_currRecDepth_134_; lean_object* v_maxRecDepth_135_; lean_object* v_ref_136_; lean_object* v_currNamespace_137_; lean_object* v_openDecls_138_; lean_object* v_initHeartbeats_139_; lean_object* v_maxHeartbeats_140_; lean_object* v_quotContext_141_; lean_object* v_currMacroScope_142_; uint8_t v_diag_143_; lean_object* v_cancelTk_x3f_144_; uint8_t v_suppressElabErrors_145_; lean_object* v_inheritedTraceOptions_146_; lean_object* v_ref_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_fileName_131_ = lean_ctor_get(v___y_128_, 0);
v_fileMap_132_ = lean_ctor_get(v___y_128_, 1);
v_options_133_ = lean_ctor_get(v___y_128_, 2);
v_currRecDepth_134_ = lean_ctor_get(v___y_128_, 3);
v_maxRecDepth_135_ = lean_ctor_get(v___y_128_, 4);
v_ref_136_ = lean_ctor_get(v___y_128_, 5);
v_currNamespace_137_ = lean_ctor_get(v___y_128_, 6);
v_openDecls_138_ = lean_ctor_get(v___y_128_, 7);
v_initHeartbeats_139_ = lean_ctor_get(v___y_128_, 8);
v_maxHeartbeats_140_ = lean_ctor_get(v___y_128_, 9);
v_quotContext_141_ = lean_ctor_get(v___y_128_, 10);
v_currMacroScope_142_ = lean_ctor_get(v___y_128_, 11);
v_diag_143_ = lean_ctor_get_uint8(v___y_128_, sizeof(void*)*14);
v_cancelTk_x3f_144_ = lean_ctor_get(v___y_128_, 12);
v_suppressElabErrors_145_ = lean_ctor_get_uint8(v___y_128_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_146_ = lean_ctor_get(v___y_128_, 13);
v_ref_147_ = l_Lean_replaceRef(v_ref_120_, v_ref_136_);
lean_inc_ref(v_inheritedTraceOptions_146_);
lean_inc(v_cancelTk_x3f_144_);
lean_inc(v_currMacroScope_142_);
lean_inc(v_quotContext_141_);
lean_inc(v_maxHeartbeats_140_);
lean_inc(v_initHeartbeats_139_);
lean_inc(v_openDecls_138_);
lean_inc(v_currNamespace_137_);
lean_inc(v_maxRecDepth_135_);
lean_inc(v_currRecDepth_134_);
lean_inc_ref(v_options_133_);
lean_inc_ref(v_fileMap_132_);
lean_inc_ref(v_fileName_131_);
v___x_148_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_148_, 0, v_fileName_131_);
lean_ctor_set(v___x_148_, 1, v_fileMap_132_);
lean_ctor_set(v___x_148_, 2, v_options_133_);
lean_ctor_set(v___x_148_, 3, v_currRecDepth_134_);
lean_ctor_set(v___x_148_, 4, v_maxRecDepth_135_);
lean_ctor_set(v___x_148_, 5, v_ref_147_);
lean_ctor_set(v___x_148_, 6, v_currNamespace_137_);
lean_ctor_set(v___x_148_, 7, v_openDecls_138_);
lean_ctor_set(v___x_148_, 8, v_initHeartbeats_139_);
lean_ctor_set(v___x_148_, 9, v_maxHeartbeats_140_);
lean_ctor_set(v___x_148_, 10, v_quotContext_141_);
lean_ctor_set(v___x_148_, 11, v_currMacroScope_142_);
lean_ctor_set(v___x_148_, 12, v_cancelTk_x3f_144_);
lean_ctor_set(v___x_148_, 13, v_inheritedTraceOptions_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*14, v_diag_143_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*14 + 1, v_suppressElabErrors_145_);
v___x_149_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_121_, v___y_126_, v___y_127_, v___x_148_, v___y_129_);
lean_dec_ref_known(v___x_148_, 14);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg___boxed(lean_object* v_ref_150_, lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_150_, v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v_ref_150_);
return v_res_161_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(lean_object* v_filter_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5));
lean_inc(v_filter_267_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7));
lean_inc(v_filter_267_);
v___x_280_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9));
lean_inc(v_filter_267_);
v___x_282_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11));
lean_inc(v_filter_267_);
v___x_284_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13));
lean_inc(v_filter_267_);
v___x_286_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15));
lean_inc(v_filter_267_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17));
lean_inc(v_filter_267_);
v___x_290_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19));
lean_inc(v_filter_267_);
v___x_292_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21));
lean_inc(v_filter_267_);
v___x_294_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23));
lean_inc(v_filter_267_);
v___x_296_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25));
lean_inc(v_filter_267_);
v___x_298_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27));
lean_inc(v_filter_267_);
v___x_300_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29));
lean_inc(v_filter_267_);
v___x_302_ = l_Lean_Syntax_isOfKind(v_filter_267_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec(v_filter_267_);
v___x_303_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v_n_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(2u);
v_n_305_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_304_);
lean_dec(v_filter_267_);
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_305_);
v___x_307_ = l_Lean_Syntax_isOfKind(v_n_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec(v_n_305_);
v___x_308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_308_;
}
else
{
lean_object* v_n_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_n_309_ = l_Lean_TSyntax_getNat(v_n_305_);
lean_dec(v_n_305_);
v___f_310_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed), 2, 1);
lean_closure_set(v___f_310_, 0, v_n_309_);
v___x_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_311_, 0, v___f_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
else
{
lean_object* v___x_313_; lean_object* v_n_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_313_ = lean_unsigned_to_nat(2u);
v_n_314_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_313_);
lean_dec(v_filter_267_);
v___x_315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_314_);
v___x_316_ = l_Lean_Syntax_isOfKind(v_n_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v_n_314_);
v___x_317_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_317_;
}
else
{
lean_object* v_n_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_n_318_ = l_Lean_TSyntax_getNat(v_n_314_);
lean_dec(v_n_314_);
v___f_319_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed), 2, 1);
lean_closure_set(v___f_319_, 0, v_n_318_);
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
lean_object* v___x_322_; lean_object* v_n_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(2u);
v_n_323_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_322_);
lean_dec(v_filter_267_);
v___x_324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_323_);
v___x_325_ = l_Lean_Syntax_isOfKind(v_n_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_n_323_);
v___x_326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_326_;
}
else
{
lean_object* v_n_327_; lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_n_327_ = l_Lean_TSyntax_getNat(v_n_323_);
lean_dec(v_n_323_);
v___f_328_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed), 2, 1);
lean_closure_set(v___f_328_, 0, v_n_327_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___f_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
else
{
lean_object* v___x_331_; lean_object* v_n_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_331_ = lean_unsigned_to_nat(2u);
v_n_332_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_331_);
lean_dec(v_filter_267_);
v___x_333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_332_);
v___x_334_ = l_Lean_Syntax_isOfKind(v_n_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_n_332_);
v___x_335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_335_;
}
else
{
lean_object* v_n_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_n_336_ = l_Lean_TSyntax_getNat(v_n_332_);
lean_dec(v_n_332_);
v___f_337_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed), 2, 1);
lean_closure_set(v___f_337_, 0, v_n_336_);
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___f_337_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
else
{
lean_object* v___x_340_; lean_object* v_n_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_340_ = lean_unsigned_to_nat(2u);
v_n_341_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_340_);
lean_dec(v_filter_267_);
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_341_);
v___x_343_ = l_Lean_Syntax_isOfKind(v_n_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_n_341_);
v___x_344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_344_;
}
else
{
lean_object* v_n_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_n_345_ = l_Lean_TSyntax_getNat(v_n_341_);
lean_dec(v_n_341_);
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
lean_object* v___x_349_; lean_object* v_n_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_349_ = lean_unsigned_to_nat(2u);
v_n_350_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_349_);
lean_dec(v_filter_267_);
v___x_351_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_350_);
v___x_352_ = l_Lean_Syntax_isOfKind(v_n_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_dec(v_n_350_);
v___x_353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_353_;
}
else
{
lean_object* v_n_354_; lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_n_354_ = l_Lean_TSyntax_getNat(v_n_350_);
lean_dec(v_n_350_);
v___f_355_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed), 2, 1);
lean_closure_set(v___f_355_, 0, v_n_354_);
v___x_356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_356_, 0, v___f_355_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
else
{
lean_object* v___x_358_; lean_object* v_n_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(2u);
v_n_359_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_358_);
lean_dec(v_filter_267_);
v___x_360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_359_);
v___x_361_ = l_Lean_Syntax_isOfKind(v_n_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec(v_n_359_);
v___x_362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_362_;
}
else
{
lean_object* v_n_363_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_n_363_ = l_Lean_TSyntax_getNat(v_n_359_);
lean_dec(v_n_359_);
v___f_364_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed), 2, 1);
lean_closure_set(v___f_364_, 0, v_n_363_);
v___x_365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_365_, 0, v___f_364_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
else
{
lean_object* v___x_367_; lean_object* v_n_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_367_ = lean_unsigned_to_nat(2u);
v_n_368_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_367_);
lean_dec(v_filter_267_);
v___x_369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31));
lean_inc(v_n_368_);
v___x_370_ = l_Lean_Syntax_isOfKind(v_n_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_n_368_);
v___x_371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_371_;
}
else
{
lean_object* v_n_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_n_372_ = l_Lean_TSyntax_getNat(v_n_368_);
lean_dec(v_n_368_);
v___f_373_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed), 2, 1);
lean_closure_set(v___f_373_, 0, v_n_372_);
v___x_374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_374_, 0, v___f_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
}
else
{
lean_object* v___x_376_; lean_object* v_a_377_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v_a_377_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_376_);
lean_dec(v_filter_267_);
v_filter_267_ = v_a_377_;
goto _start;
}
}
else
{
lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_381_; 
v___x_379_ = lean_unsigned_to_nat(1u);
v_a_380_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_379_);
lean_dec(v_filter_267_);
v___x_381_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_380_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_386_, 0, v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
return v___x_381_;
}
}
}
else
{
lean_object* v___x_391_; lean_object* v_a_392_; lean_object* v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v_a_392_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_391_);
v___x_393_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_392_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; lean_object* v_b_396_; lean_object* v___x_397_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = lean_unsigned_to_nat(2u);
v_b_396_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_395_);
lean_dec(v_filter_267_);
v___x_397_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_396_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_402_, 0, v_a_394_);
lean_ctor_set(v___x_402_, 1, v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_dec(v_a_394_);
return v___x_397_;
}
}
else
{
lean_dec(v_filter_267_);
return v___x_393_;
}
}
}
else
{
lean_object* v___x_407_; lean_object* v_a_408_; lean_object* v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v_a_408_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_407_);
v___x_409_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_408_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v_b_412_; lean_object* v___x_413_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = lean_unsigned_to_nat(2u);
v_b_412_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_411_);
lean_dec(v_filter_267_);
v___x_413_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_412_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_422_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_422_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_418_, 0, v_a_410_);
lean_ctor_set(v___x_418_, 1, v_a_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_dec(v_a_410_);
return v___x_413_;
}
}
else
{
lean_dec(v_filter_267_);
return v___x_409_;
}
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = l_Lean_Syntax_getArg(v_filter_267_, v___x_423_);
lean_dec(v_filter_267_);
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33));
lean_inc(v___x_424_);
v___x_426_ = l_Lean_Syntax_isOfKind(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec(v___x_424_);
v___x_427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
return v___x_427_;
}
else
{
lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34));
v___x_429_ = 0;
lean_inc(v___x_424_);
v___x_430_ = l_Lean_Elab_Term_resolveId_x3f(v___x_424_, v___x_428_, v___x_429_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_465_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_465_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_465_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_465_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; 
if (lean_obj_tag(v_a_431_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_464_; 
v_val_446_ = lean_ctor_get(v_a_431_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_464_ == 0)
{
v___x_448_ = v_a_431_;
v_isShared_449_ = v_isSharedCheck_464_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_a_431_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_464_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
switch(lean_obj_tag(v_val_446_))
{
case 4:
{
lean_object* v_declName_450_; lean_object* v___x_452_; 
lean_dec(v___x_424_);
v_declName_450_ = lean_ctor_get(v_val_446_, 0);
lean_inc(v_declName_450_);
lean_dec_ref_known(v_val_446_, 2);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_declName_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_declName_450_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_452_);
v___x_454_ = v___x_433_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
case 1:
{
lean_object* v_fvarId_457_; lean_object* v___x_459_; 
lean_dec(v___x_424_);
v_fvarId_457_ = lean_ctor_get(v_val_446_, 0);
lean_inc(v_fvarId_457_);
lean_dec_ref_known(v_val_446_, 1);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 2);
lean_ctor_set(v___x_448_, 0, v_fvarId_457_);
v___x_459_ = v___x_448_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fvarId_457_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_459_);
v___x_461_ = v___x_433_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
default: 
{
lean_del_object(v___x_448_);
lean_dec(v_val_446_);
lean_del_object(v___x_433_);
v___y_436_ = v_a_268_;
v___y_437_ = v_a_269_;
v___y_438_ = v_a_270_;
v___y_439_ = v_a_271_;
v___y_440_ = v_a_272_;
v___y_441_ = v_a_273_;
v___y_442_ = v_a_274_;
v___y_443_ = v_a_275_;
goto v___jp_435_;
}
}
}
}
else
{
lean_del_object(v___x_433_);
lean_dec(v_a_431_);
v___y_436_ = v_a_268_;
v___y_437_ = v_a_269_;
v___y_438_ = v_a_270_;
v___y_439_ = v_a_271_;
v___y_440_ = v_a_272_;
v___y_441_ = v_a_273_;
v___y_442_ = v_a_274_;
v___y_443_ = v_a_275_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36, &l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36_once, _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36);
v___x_445_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v___x_424_, v___x_444_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___x_424_);
return v___x_445_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v___x_424_);
v_a_466_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_430_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_430_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___boxed(lean_object* v_filter_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_filter_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(lean_object* v_00_u03b1_485_, lean_object* v_ref_486_, lean_object* v_msg_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_486_, v_msg_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___boxed(lean_object* v_00_u03b1_498_, lean_object* v_ref_499_, lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(v_00_u03b1_498_, v_ref_499_, v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v_ref_499_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(lean_object* v_00_u03b1_511_, lean_object* v_msg_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_512_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_523_, lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(v_00_u03b1_523_, v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter(lean_object* v_filter_x3f_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
if (lean_obj_tag(v_filter_x3f_535_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_546_; 
v_val_545_ = lean_ctor_get(v_filter_x3f_535_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_filter_x3f_535_, 1);
v___x_546_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_val_545_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_filter_x3f_535_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabFilter___boxed(lean_object* v_filter_x3f_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_559_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
