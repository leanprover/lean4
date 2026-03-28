// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Basic
// Imports: public import Init.Data.Range.Polymorphic.PRange public import Init.Data.Option.Instances
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Option_decidableForallMem___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_isEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_isEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rco_isEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_isEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rco_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rci_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roc_isEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roc_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roi_isEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roi_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Ric_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rii_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Rii_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticGet_elem_tactic_extensible"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 80, 20, 121, 148, 193, 237, 106)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Std.Rco.Internal.get_elem_helper_upper_open"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rco"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "get_elem_helper_upper_open"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(82, 23, 146, 9, 98, 233, 127, 0)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(235, 20, 34, 81, 170, 144, 60, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(96, 135, 33, 90, 224, 38, 48, 119)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term‹_›"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(149, 139, 117, 210, 91, 226, 103, 115)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "‹"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "›"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PRange"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(74, 11, 109, 218, 234, 5, 175, 136)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticTrivial"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(91, 113, 211, 1, 53, 106, 100, 38)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Std.Roo.Internal.get_elem_helper_upper_open"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roo"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(142, 134, 1, 143, 80, 181, 102, 249)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(223, 82, 185, 228, 36, 97, 82, 247)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(100, 210, 123, 100, 109, 65, 141, 188)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Std.Rio.Internal.get_elem_helper_upper_open"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rio"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(129, 16, 150, 7, 181, 46, 199, 145)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(28, 143, 202, 126, 119, 155, 55, 201)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(99, 142, 112, 90, 67, 68, 27, 126)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_isEmpty___redArg(lean_object* v_inst_1_, lean_object* v_r_2_){
_start:
{
lean_object* v_lower_3_; lean_object* v_upper_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_lower_3_ = lean_ctor_get(v_r_2_, 0);
lean_inc(v_lower_3_);
v_upper_4_ = lean_ctor_get(v_r_2_, 1);
lean_inc(v_upper_4_);
lean_dec_ref(v_r_2_);
v___x_5_ = lean_apply_2(v_inst_1_, v_lower_3_, v_upper_4_);
v___x_6_ = lean_unbox(v___x_5_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_isEmpty___redArg___boxed(lean_object* v_inst_9_, lean_object* v_r_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_Rcc_isEmpty___redArg(v_inst_9_, v_r_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_isEmpty(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_r_17_){
_start:
{
lean_object* v_lower_18_; lean_object* v_upper_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v_lower_18_ = lean_ctor_get(v_r_17_, 0);
lean_inc(v_lower_18_);
v_upper_19_ = lean_ctor_get(v_r_17_, 1);
lean_inc(v_upper_19_);
lean_dec_ref(v_r_17_);
v___x_20_ = lean_apply_2(v_inst_15_, v_lower_18_, v_upper_19_);
v___x_21_ = lean_unbox(v___x_20_);
if (v___x_21_ == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 1;
return v___x_22_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_isEmpty___boxed(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_r_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_Rcc_isEmpty(v_00_u03b1_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_r_28_);
lean_dec_ref(v_inst_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_isEmpty___redArg(lean_object* v_inst_31_, lean_object* v_r_32_){
_start:
{
lean_object* v_lower_33_; lean_object* v_upper_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_lower_33_ = lean_ctor_get(v_r_32_, 0);
lean_inc(v_lower_33_);
v_upper_34_ = lean_ctor_get(v_r_32_, 1);
lean_inc(v_upper_34_);
lean_dec_ref(v_r_32_);
v___x_35_ = lean_apply_2(v_inst_31_, v_lower_33_, v_upper_34_);
v___x_36_ = lean_unbox(v___x_35_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; 
v___x_37_ = 1;
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_isEmpty___redArg___boxed(lean_object* v_inst_39_, lean_object* v_r_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Rco_isEmpty___redArg(v_inst_39_, v_r_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_isEmpty(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_r_47_){
_start:
{
lean_object* v_lower_48_; lean_object* v_upper_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_lower_48_ = lean_ctor_get(v_r_47_, 0);
lean_inc(v_lower_48_);
v_upper_49_ = lean_ctor_get(v_r_47_, 1);
lean_inc(v_upper_49_);
lean_dec_ref(v_r_47_);
v___x_50_ = lean_apply_2(v_inst_45_, v_lower_48_, v_upper_49_);
v___x_51_ = lean_unbox(v___x_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_isEmpty___boxed(lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_r_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_Rco_isEmpty(v_00_u03b1_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_r_58_);
lean_dec_ref(v_inst_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_isEmpty(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_x_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___boxed(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Std_Rci_isEmpty(v_00_u03b1_65_, v_inst_66_, v_x_67_);
lean_dec(v_x_67_);
lean_dec_ref(v_inst_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_isEmpty___redArg(lean_object* v_inst_70_, lean_object* v_r_71_){
_start:
{
lean_object* v_lower_72_; lean_object* v_upper_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_lower_72_ = lean_ctor_get(v_r_71_, 0);
lean_inc(v_lower_72_);
v_upper_73_ = lean_ctor_get(v_r_71_, 1);
lean_inc(v_upper_73_);
lean_dec_ref(v_r_71_);
v___x_74_ = lean_apply_2(v_inst_70_, v_lower_72_, v_upper_73_);
v___x_75_ = lean_unbox(v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___redArg___boxed(lean_object* v_inst_78_, lean_object* v_r_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Std_Roc_isEmpty___redArg(v_inst_78_, v_r_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_isEmpty(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_r_86_){
_start:
{
lean_object* v_lower_87_; lean_object* v_upper_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_lower_87_ = lean_ctor_get(v_r_86_, 0);
lean_inc(v_lower_87_);
v_upper_88_ = lean_ctor_get(v_r_86_, 1);
lean_inc(v_upper_88_);
lean_dec_ref(v_r_86_);
v___x_89_ = lean_apply_2(v_inst_84_, v_lower_87_, v_upper_88_);
v___x_90_ = lean_unbox(v___x_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___boxed(lean_object* v_00_u03b1_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_r_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Std_Roc_isEmpty(v_00_u03b1_93_, v_inst_94_, v_inst_95_, v_inst_96_, v_r_97_);
lean_dec_ref(v_inst_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty___redArg___lam__0(lean_object* v_inst_100_, lean_object* v_upper_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_apply_2(v_inst_100_, v_a_102_, v_upper_101_);
v___x_104_ = lean_unbox(v___x_103_);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___lam__0___boxed(lean_object* v_inst_107_, lean_object* v_upper_108_, lean_object* v_a_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Roo_isEmpty___redArg___lam__0(v_inst_107_, v_upper_108_, v_a_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty___redArg(lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_r_114_){
_start:
{
lean_object* v_succ_x3f_115_; lean_object* v_lower_116_; lean_object* v_upper_117_; lean_object* v___f_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_succ_x3f_115_ = lean_ctor_get(v_inst_113_, 0);
lean_inc_ref(v_succ_x3f_115_);
lean_dec_ref(v_inst_113_);
v_lower_116_ = lean_ctor_get(v_r_114_, 0);
lean_inc(v_lower_116_);
v_upper_117_ = lean_ctor_get(v_r_114_, 1);
lean_inc(v_upper_117_);
lean_dec_ref(v_r_114_);
v___f_118_ = lean_alloc_closure((void*)(l_Std_Roo_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_118_, 0, v_inst_112_);
lean_closure_set(v___f_118_, 1, v_upper_117_);
v___x_119_ = lean_apply_1(v_succ_x3f_115_, v_lower_116_);
v___x_120_ = l_Option_decidableForallMem___redArg(v___f_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___boxed(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_r_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_Roo_isEmpty___redArg(v_inst_121_, v_inst_122_, v_r_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty(lean_object* v_00_u03b1_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_r_130_){
_start:
{
lean_object* v_succ_x3f_131_; lean_object* v_lower_132_; lean_object* v_upper_133_; lean_object* v___f_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_succ_x3f_131_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_succ_x3f_131_);
lean_dec_ref(v_inst_129_);
v_lower_132_ = lean_ctor_get(v_r_130_, 0);
lean_inc(v_lower_132_);
v_upper_133_ = lean_ctor_get(v_r_130_, 1);
lean_inc(v_upper_133_);
lean_dec_ref(v_r_130_);
v___f_134_ = lean_alloc_closure((void*)(l_Std_Roo_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_134_, 0, v_inst_128_);
lean_closure_set(v___f_134_, 1, v_upper_133_);
v___x_135_ = lean_apply_1(v_succ_x3f_131_, v_lower_132_);
v___x_136_ = l_Option_decidableForallMem___redArg(v___f_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___boxed(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_r_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Std_Roo_isEmpty(v_00_u03b1_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_r_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_isEmpty___redArg(lean_object* v_inst_144_, lean_object* v_r_145_){
_start:
{
lean_object* v_succ_x3f_146_; lean_object* v___x_147_; 
v_succ_x3f_146_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_succ_x3f_146_);
lean_dec_ref(v_inst_144_);
v___x_147_ = lean_apply_1(v_succ_x3f_146_, v_r_145_);
if (lean_obj_tag(v___x_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 1;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec_ref(v___x_147_);
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___redArg___boxed(lean_object* v_inst_150_, lean_object* v_r_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Std_Roi_isEmpty___redArg(v_inst_150_, v_r_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_isEmpty(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_r_156_){
_start:
{
lean_object* v_succ_x3f_157_; lean_object* v___x_158_; 
v_succ_x3f_157_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_succ_x3f_157_);
lean_dec_ref(v_inst_155_);
v___x_158_ = lean_apply_1(v_succ_x3f_157_, v_r_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
uint8_t v___x_159_; 
v___x_159_ = 1;
return v___x_159_;
}
else
{
uint8_t v___x_160_; 
lean_dec_ref(v___x_158_);
v___x_160_ = 0;
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___boxed(lean_object* v_00_u03b1_161_, lean_object* v_inst_162_, lean_object* v_r_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_Roi_isEmpty(v_00_u03b1_161_, v_inst_162_, v_r_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_isEmpty(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_x_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___boxed(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_Ric_isEmpty(v_00_u03b1_170_, v_inst_171_, v_x_172_);
lean_dec(v_x_172_);
lean_dec_ref(v_inst_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty___redArg___lam__0(lean_object* v_inst_175_, lean_object* v_r_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_apply_2(v_inst_175_, v_a_177_, v_r_176_);
v___x_179_ = lean_unbox(v___x_178_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 1;
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___lam__0___boxed(lean_object* v_inst_182_, lean_object* v_r_183_, lean_object* v_a_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_Rio_isEmpty___redArg___lam__0(v_inst_182_, v_r_183_, v_a_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty___redArg(lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_r_189_){
_start:
{
lean_object* v___f_190_; uint8_t v___x_191_; 
v___f_190_ = lean_alloc_closure((void*)(l_Std_Rio_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_190_, 0, v_inst_187_);
lean_closure_set(v___f_190_, 1, v_r_189_);
v___x_191_ = l_Option_decidableForallMem___redArg(v___f_190_, v_inst_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___boxed(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_r_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_Rio_isEmpty___redArg(v_inst_192_, v_inst_193_, v_r_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty(lean_object* v_00_u03b1_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_r_202_){
_start:
{
lean_object* v___f_203_; uint8_t v___x_204_; 
v___f_203_ = lean_alloc_closure((void*)(l_Std_Rio_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_203_, 0, v_inst_199_);
lean_closure_set(v___f_203_, 1, v_r_202_);
v___x_204_ = l_Option_decidableForallMem___redArg(v___f_203_, v_inst_201_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___boxed(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_r_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_Rio_isEmpty(v_00_u03b1_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_inst_209_, v_r_210_);
lean_dec_ref(v_inst_208_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_isEmpty___redArg(lean_object* v_inst_213_){
_start:
{
if (lean_obj_tag(v_inst_213_) == 0)
{
uint8_t v___x_214_; 
v___x_214_ = 1;
return v___x_214_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = 0;
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___redArg___boxed(lean_object* v_inst_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Std_Rii_isEmpty___redArg(v_inst_216_);
lean_dec(v_inst_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_isEmpty(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_inst_220_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 1;
return v___x_222_;
}
else
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___boxed(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_Rii_isEmpty(v_00_u03b1_224_, v_inst_225_, v_x_226_);
lean_dec(v_inst_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21));
v___x_275_ = l_String_toRawSubstring_x27(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44));
v___x_321_ = l_String_toRawSubstring_x27(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60));
v___x_355_ = l_String_toRawSubstring_x27(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66));
v___x_370_ = l_String_toRawSubstring_x27(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_393_ = l_Lean_Syntax_isOfKind(v_x_389_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_box(1);
v___x_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_a_391_);
return v___x_395_;
}
else
{
lean_object* v_quotContext_396_; lean_object* v_currMacroScope_397_; lean_object* v_ref_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_quotContext_396_ = lean_ctor_get(v_a_390_, 1);
v_currMacroScope_397_ = lean_ctor_get(v_a_390_, 2);
v_ref_398_ = lean_ctor_get(v_a_390_, 5);
v___x_399_ = 0;
v___x_400_ = l_Lean_SourceInfo_fromRef(v_ref_398_, v___x_399_);
v___x_401_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
v___x_402_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
lean_inc_n(v___x_400_, 50);
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_400_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
v___x_404_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_405_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_406_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11));
v___x_407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_400_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
v___x_409_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
v___x_410_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
v___x_411_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_400_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
v___x_413_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
v___x_414_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22);
v___x_415_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27));
lean_inc_n(v_currMacroScope_397_, 4);
lean_inc_n(v_quotContext_396_, 4);
v___x_416_ = l_Lean_addMacroScope(v_quotContext_396_, v___x_415_, v_currMacroScope_397_);
v___x_417_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29));
v___x_418_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_418_, 0, v___x_400_);
lean_ctor_set(v___x_418_, 1, v___x_414_);
lean_ctor_set(v___x_418_, 2, v___x_416_);
lean_ctor_set(v___x_418_, 3, v___x_417_);
v___x_419_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31));
v___x_420_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32));
v___x_421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_400_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34));
v___x_423_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35));
v___x_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_400_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_Syntax_node1(v___x_400_, v___x_422_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36));
v___x_427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_400_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Syntax_node3(v___x_400_, v___x_419_, v___x_421_, v___x_425_, v___x_427_);
v___x_429_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38));
v___x_430_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40));
v___x_431_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41));
v___x_432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_400_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43));
v___x_434_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45);
v___x_435_ = lean_box(0);
v___x_436_ = l_Lean_addMacroScope(v_quotContext_396_, v___x_435_, v_currMacroScope_397_);
v___x_437_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52));
v___x_438_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_438_, 0, v___x_400_);
lean_ctor_set(v___x_438_, 1, v___x_434_);
lean_ctor_set(v___x_438_, 2, v___x_436_);
lean_ctor_set(v___x_438_, 3, v___x_437_);
v___x_439_ = l_Lean_Syntax_node1(v___x_400_, v___x_433_, v___x_438_);
v___x_440_ = l_Lean_Syntax_node2(v___x_400_, v___x_430_, v___x_432_, v___x_439_);
v___x_441_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54));
v___x_442_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55));
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_400_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57));
v___x_445_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58));
v___x_446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_400_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = l_Lean_Syntax_node1(v___x_400_, v___x_444_, v___x_446_);
v___x_448_ = l_Lean_Syntax_node1(v___x_400_, v___x_404_, v___x_447_);
v___x_449_ = l_Lean_Syntax_node1(v___x_400_, v___x_409_, v___x_448_);
v___x_450_ = l_Lean_Syntax_node1(v___x_400_, v___x_408_, v___x_449_);
v___x_451_ = l_Lean_Syntax_node2(v___x_400_, v___x_441_, v___x_443_, v___x_450_);
v___x_452_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59));
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_400_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_Syntax_node3(v___x_400_, v___x_429_, v___x_440_, v___x_451_, v___x_453_);
v___x_455_ = l_Lean_Syntax_node2(v___x_400_, v___x_404_, v___x_428_, v___x_454_);
lean_inc_n(v___x_455_, 2);
v___x_456_ = l_Lean_Syntax_node2(v___x_400_, v___x_413_, v___x_418_, v___x_455_);
lean_inc_ref_n(v___x_412_, 2);
v___x_457_ = l_Lean_Syntax_node2(v___x_400_, v___x_411_, v___x_412_, v___x_456_);
v___x_458_ = l_Lean_Syntax_node1(v___x_400_, v___x_404_, v___x_457_);
v___x_459_ = l_Lean_Syntax_node1(v___x_400_, v___x_409_, v___x_458_);
v___x_460_ = l_Lean_Syntax_node1(v___x_400_, v___x_408_, v___x_459_);
lean_inc_ref_n(v___x_407_, 3);
v___x_461_ = l_Lean_Syntax_node2(v___x_400_, v___x_405_, v___x_407_, v___x_460_);
v___x_462_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61);
v___x_463_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63));
v___x_464_ = l_Lean_addMacroScope(v_quotContext_396_, v___x_463_, v_currMacroScope_397_);
v___x_465_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65));
v___x_466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_466_, 0, v___x_400_);
lean_ctor_set(v___x_466_, 1, v___x_462_);
lean_ctor_set(v___x_466_, 2, v___x_464_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
v___x_467_ = l_Lean_Syntax_node2(v___x_400_, v___x_413_, v___x_466_, v___x_455_);
v___x_468_ = l_Lean_Syntax_node2(v___x_400_, v___x_411_, v___x_412_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_400_, v___x_404_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v___x_400_, v___x_409_, v___x_469_);
v___x_471_ = l_Lean_Syntax_node1(v___x_400_, v___x_408_, v___x_470_);
v___x_472_ = l_Lean_Syntax_node2(v___x_400_, v___x_405_, v___x_407_, v___x_471_);
v___x_473_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67);
v___x_474_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69));
v___x_475_ = l_Lean_addMacroScope(v_quotContext_396_, v___x_474_, v_currMacroScope_397_);
v___x_476_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71));
v___x_477_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_477_, 0, v___x_400_);
lean_ctor_set(v___x_477_, 1, v___x_473_);
lean_ctor_set(v___x_477_, 2, v___x_475_);
lean_ctor_set(v___x_477_, 3, v___x_476_);
v___x_478_ = l_Lean_Syntax_node2(v___x_400_, v___x_413_, v___x_477_, v___x_455_);
v___x_479_ = l_Lean_Syntax_node2(v___x_400_, v___x_411_, v___x_412_, v___x_478_);
v___x_480_ = l_Lean_Syntax_node1(v___x_400_, v___x_404_, v___x_479_);
v___x_481_ = l_Lean_Syntax_node1(v___x_400_, v___x_409_, v___x_480_);
v___x_482_ = l_Lean_Syntax_node1(v___x_400_, v___x_408_, v___x_481_);
v___x_483_ = l_Lean_Syntax_node2(v___x_400_, v___x_405_, v___x_407_, v___x_482_);
v___x_484_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72));
v___x_485_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73));
v___x_486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_400_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
v___x_487_ = l_Lean_Syntax_node1(v___x_400_, v___x_485_, v___x_486_);
v___x_488_ = l_Lean_Syntax_node1(v___x_400_, v___x_404_, v___x_487_);
v___x_489_ = l_Lean_Syntax_node1(v___x_400_, v___x_409_, v___x_488_);
v___x_490_ = l_Lean_Syntax_node1(v___x_400_, v___x_408_, v___x_489_);
v___x_491_ = l_Lean_Syntax_node2(v___x_400_, v___x_405_, v___x_407_, v___x_490_);
v___x_492_ = l_Lean_Syntax_node4(v___x_400_, v___x_404_, v___x_461_, v___x_472_, v___x_483_, v___x_491_);
v___x_493_ = l_Lean_Syntax_node2(v___x_400_, v___x_402_, v___x_403_, v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v_a_391_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object* v_x_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_495_, v_a_496_, v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_498_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
