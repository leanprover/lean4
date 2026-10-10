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
LEAN_EXPORT uint8_t l_Std_Rci_isEmpty___redArg();
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Ric_isEmpty___redArg();
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___redArg___boxed(lean_object*);
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
uint8_t l_Std_Rcc_isEmpty___redArg(lean_object* v_inst_1_, lean_object* v_r_2_){
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
LEAN_EXPORT void l_Std_Rcc_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_r_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_Std_Rcc_isEmpty___redArg(v_inst_1_, v_r_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Std_Rcc_isEmpty___redArg___boxed(lean_object* v_inst_10_, lean_object* v_r_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_Rcc_isEmpty___redArg(v_inst_10_, v_r_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_Std_Rcc_isEmpty(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_r_18_){
_start:
{
lean_object* v_lower_19_; lean_object* v_upper_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_lower_19_ = lean_ctor_get(v_r_18_, 0);
lean_inc(v_lower_19_);
v_upper_20_ = lean_ctor_get(v_r_18_, 1);
lean_inc(v_upper_20_);
lean_dec_ref(v_r_18_);
v___x_21_ = lean_apply_2(v_inst_16_, v_lower_19_, v_upper_20_);
v___x_22_ = lean_unbox(v___x_21_);
if (v___x_22_ == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 1;
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
}
}
LEAN_EXPORT void l_Std_Rcc_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_15_ = stack[1].m_obj;
lean_object* v_inst_16_ = stack[2].m_obj;
lean_object* v_inst_17_ = stack[3].m_obj;
lean_object* v_r_18_ = stack[4].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Std_Rcc_isEmpty(lean_box(0), v_inst_15_, v_inst_16_, v_inst_17_, v_r_18_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Std_Rcc_isEmpty___boxed(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_r_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Std_Rcc_isEmpty(v_00_u03b1_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_r_30_);
lean_dec_ref(v_inst_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
uint8_t l_Std_Rco_isEmpty___redArg(lean_object* v_inst_33_, lean_object* v_r_34_){
_start:
{
lean_object* v_lower_35_; lean_object* v_upper_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_lower_35_ = lean_ctor_get(v_r_34_, 0);
lean_inc(v_lower_35_);
v_upper_36_ = lean_ctor_get(v_r_34_, 1);
lean_inc(v_upper_36_);
lean_dec_ref(v_r_34_);
v___x_37_ = lean_apply_2(v_inst_33_, v_lower_35_, v_upper_36_);
v___x_38_ = lean_unbox(v___x_37_);
if (v___x_38_ == 0)
{
uint8_t v___x_39_; 
v___x_39_ = 1;
return v___x_39_;
}
else
{
uint8_t v___x_40_; 
v___x_40_ = 0;
return v___x_40_;
}
}
}
LEAN_EXPORT void l_Std_Rco_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_33_ = stack[0].m_obj;
lean_object* v_r_34_ = stack[1].m_obj;
uint8_t v_res_41_;
v_res_41_ = l_Std_Rco_isEmpty___redArg(v_inst_33_, v_r_34_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_Std_Rco_isEmpty___redArg___boxed(lean_object* v_inst_42_, lean_object* v_r_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_Rco_isEmpty___redArg(v_inst_42_, v_r_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
uint8_t l_Std_Rco_isEmpty(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_r_50_){
_start:
{
lean_object* v_lower_51_; lean_object* v_upper_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v_lower_51_ = lean_ctor_get(v_r_50_, 0);
lean_inc(v_lower_51_);
v_upper_52_ = lean_ctor_get(v_r_50_, 1);
lean_inc(v_upper_52_);
lean_dec_ref(v_r_50_);
v___x_53_ = lean_apply_2(v_inst_48_, v_lower_51_, v_upper_52_);
v___x_54_ = lean_unbox(v___x_53_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
LEAN_EXPORT void l_Std_Rco_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_47_ = stack[1].m_obj;
lean_object* v_inst_48_ = stack[2].m_obj;
lean_object* v_inst_49_ = stack[3].m_obj;
lean_object* v_r_50_ = stack[4].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_Rco_isEmpty(lean_box(0), v_inst_47_, v_inst_48_, v_inst_49_, v_r_50_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_Rco_isEmpty___boxed(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_r_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Std_Rco_isEmpty(v_00_u03b1_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_r_62_);
lean_dec_ref(v_inst_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
uint8_t l_Std_Rci_isEmpty___redArg(){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
LEAN_EXPORT void l_Std_Rci_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_67_;
v_res_67_ = l_Std_Rci_isEmpty___redArg();
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___redArg___boxed(lean_object* v___dummy_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Std_Rci_isEmpty___redArg();
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
uint8_t l_Std_Rci_isEmpty(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_x_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_Rci_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_72_ = stack[1].m_obj;
lean_object* v_x_73_ = stack[2].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_Std_Rci_isEmpty(lean_box(0), v_inst_72_, v_x_73_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___boxed(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Std_Rci_isEmpty(v_00_u03b1_76_, v_inst_77_, v_x_78_);
lean_dec(v_x_78_);
lean_dec_ref(v_inst_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
uint8_t l_Std_Roc_isEmpty___redArg(lean_object* v_inst_81_, lean_object* v_r_82_){
_start:
{
lean_object* v_lower_83_; lean_object* v_upper_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_lower_83_ = lean_ctor_get(v_r_82_, 0);
lean_inc(v_lower_83_);
v_upper_84_ = lean_ctor_get(v_r_82_, 1);
lean_inc(v_upper_84_);
lean_dec_ref(v_r_82_);
v___x_85_ = lean_apply_2(v_inst_81_, v_lower_83_, v_upper_84_);
v___x_86_ = lean_unbox(v___x_85_);
if (v___x_86_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT void l_Std_Roc_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_81_ = stack[0].m_obj;
lean_object* v_r_82_ = stack[1].m_obj;
uint8_t v_res_89_;
v_res_89_ = l_Std_Roc_isEmpty___redArg(v_inst_81_, v_r_82_);
stack->m_num = v_res_89_;
}
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___redArg___boxed(lean_object* v_inst_90_, lean_object* v_r_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_Roc_isEmpty___redArg(v_inst_90_, v_r_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l_Std_Roc_isEmpty(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_r_98_){
_start:
{
lean_object* v_lower_99_; lean_object* v_upper_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_lower_99_ = lean_ctor_get(v_r_98_, 0);
lean_inc(v_lower_99_);
v_upper_100_ = lean_ctor_get(v_r_98_, 1);
lean_inc(v_upper_100_);
lean_dec_ref(v_r_98_);
v___x_101_ = lean_apply_2(v_inst_96_, v_lower_99_, v_upper_100_);
v___x_102_ = lean_unbox(v___x_101_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT void l_Std_Roc_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_95_ = stack[1].m_obj;
lean_object* v_inst_96_ = stack[2].m_obj;
lean_object* v_inst_97_ = stack[3].m_obj;
lean_object* v_r_98_ = stack[4].m_obj;
uint8_t v_res_105_;
v_res_105_ = l_Std_Roc_isEmpty(lean_box(0), v_inst_95_, v_inst_96_, v_inst_97_, v_r_98_);
stack->m_num = v_res_105_;
}
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___boxed(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_r_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Std_Roc_isEmpty(v_00_u03b1_106_, v_inst_107_, v_inst_108_, v_inst_109_, v_r_110_);
lean_dec_ref(v_inst_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
uint8_t l_Std_Roo_isEmpty___redArg___lam__0(lean_object* v_inst_113_, lean_object* v_upper_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_apply_2(v_inst_113_, v_a_115_, v_upper_114_);
v___x_117_ = lean_unbox(v___x_116_);
if (v___x_117_ == 0)
{
uint8_t v___x_118_; 
v___x_118_ = 1;
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
}
LEAN_EXPORT void l_Std_Roo_isEmpty___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_113_ = stack[0].m_obj;
lean_object* v_upper_114_ = stack[1].m_obj;
lean_object* v_a_115_ = stack[2].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Std_Roo_isEmpty___redArg___lam__0(v_inst_113_, v_upper_114_, v_a_115_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___lam__0___boxed(lean_object* v_inst_121_, lean_object* v_upper_122_, lean_object* v_a_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_Roo_isEmpty___redArg___lam__0(v_inst_121_, v_upper_122_, v_a_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
uint8_t l_Std_Roo_isEmpty___redArg(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_r_128_){
_start:
{
lean_object* v_succ_x3f_129_; lean_object* v_lower_130_; lean_object* v_upper_131_; lean_object* v___f_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_succ_x3f_129_ = lean_ctor_get(v_inst_127_, 0);
lean_inc_ref(v_succ_x3f_129_);
lean_dec_ref(v_inst_127_);
v_lower_130_ = lean_ctor_get(v_r_128_, 0);
lean_inc(v_lower_130_);
v_upper_131_ = lean_ctor_get(v_r_128_, 1);
lean_inc(v_upper_131_);
lean_dec_ref(v_r_128_);
v___f_132_ = lean_alloc_closure((void*)(l_Std_Roo_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_132_, 0, v_inst_126_);
lean_closure_set(v___f_132_, 1, v_upper_131_);
v___x_133_ = lean_apply_1(v_succ_x3f_129_, v_lower_130_);
v___x_134_ = l_Option_decidableForallMem___redArg(v___f_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT void l_Std_Roo_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_126_ = stack[0].m_obj;
lean_object* v_inst_127_ = stack[1].m_obj;
lean_object* v_r_128_ = stack[2].m_obj;
uint8_t v_res_135_;
v_res_135_ = l_Std_Roo_isEmpty___redArg(v_inst_126_, v_inst_127_, v_r_128_);
stack->m_num = v_res_135_;
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___boxed(lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_r_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_Roo_isEmpty___redArg(v_inst_136_, v_inst_137_, v_r_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
uint8_t l_Std_Roo_isEmpty(lean_object* v_00_u03b1_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_r_145_){
_start:
{
lean_object* v_succ_x3f_146_; lean_object* v_lower_147_; lean_object* v_upper_148_; lean_object* v___f_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_succ_x3f_146_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_succ_x3f_146_);
lean_dec_ref(v_inst_144_);
v_lower_147_ = lean_ctor_get(v_r_145_, 0);
lean_inc(v_lower_147_);
v_upper_148_ = lean_ctor_get(v_r_145_, 1);
lean_inc(v_upper_148_);
lean_dec_ref(v_r_145_);
v___f_149_ = lean_alloc_closure((void*)(l_Std_Roo_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_149_, 0, v_inst_143_);
lean_closure_set(v___f_149_, 1, v_upper_148_);
v___x_150_ = lean_apply_1(v_succ_x3f_146_, v_lower_147_);
v___x_151_ = l_Option_decidableForallMem___redArg(v___f_149_, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT void l_Std_Roo_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_142_ = stack[1].m_obj;
lean_object* v_inst_143_ = stack[2].m_obj;
lean_object* v_inst_144_ = stack[3].m_obj;
lean_object* v_r_145_ = stack[4].m_obj;
uint8_t v_res_152_;
v_res_152_ = l_Std_Roo_isEmpty(lean_box(0), v_inst_142_, v_inst_143_, v_inst_144_, v_r_145_);
stack->m_num = v_res_152_;
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___boxed(lean_object* v_00_u03b1_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_r_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_Roo_isEmpty(v_00_u03b1_153_, v_inst_154_, v_inst_155_, v_inst_156_, v_r_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
uint8_t l_Std_Roi_isEmpty___redArg(lean_object* v_inst_160_, lean_object* v_r_161_){
_start:
{
lean_object* v_succ_x3f_162_; lean_object* v___x_163_; 
v_succ_x3f_162_ = lean_ctor_get(v_inst_160_, 0);
lean_inc_ref(v_succ_x3f_162_);
lean_dec_ref(v_inst_160_);
v___x_163_ = lean_apply_1(v_succ_x3f_162_, v_r_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = 0;
return v___x_165_;
}
}
}
LEAN_EXPORT void l_Std_Roi_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_160_ = stack[0].m_obj;
lean_object* v_r_161_ = stack[1].m_obj;
uint8_t v_res_166_;
v_res_166_ = l_Std_Roi_isEmpty___redArg(v_inst_160_, v_r_161_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___redArg___boxed(lean_object* v_inst_167_, lean_object* v_r_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_Roi_isEmpty___redArg(v_inst_167_, v_r_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
uint8_t l_Std_Roi_isEmpty(lean_object* v_00_u03b1_171_, lean_object* v_inst_172_, lean_object* v_r_173_){
_start:
{
lean_object* v_succ_x3f_174_; lean_object* v___x_175_; 
v_succ_x3f_174_ = lean_ctor_get(v_inst_172_, 0);
lean_inc_ref(v_succ_x3f_174_);
lean_dec_ref(v_inst_172_);
v___x_175_ = lean_apply_1(v_succ_x3f_174_, v_r_173_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = 1;
return v___x_176_;
}
else
{
uint8_t v___x_177_; 
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = 0;
return v___x_177_;
}
}
}
LEAN_EXPORT void l_Std_Roi_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_172_ = stack[1].m_obj;
lean_object* v_r_173_ = stack[2].m_obj;
uint8_t v_res_178_;
v_res_178_ = l_Std_Roi_isEmpty(lean_box(0), v_inst_172_, v_r_173_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___boxed(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_r_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Std_Roi_isEmpty(v_00_u03b1_179_, v_inst_180_, v_r_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
uint8_t l_Std_Ric_isEmpty___redArg(){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
LEAN_EXPORT void l_Std_Ric_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_186_;
v_res_186_ = l_Std_Ric_isEmpty___redArg();
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___redArg___boxed(lean_object* v___dummy_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Std_Ric_isEmpty___redArg();
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
uint8_t l_Std_Ric_isEmpty(lean_object* v_00_u03b1_190_, lean_object* v_inst_191_, lean_object* v_x_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
LEAN_EXPORT void l_Std_Ric_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_191_ = stack[1].m_obj;
lean_object* v_x_192_ = stack[2].m_obj;
uint8_t v_res_194_;
v_res_194_ = l_Std_Ric_isEmpty(lean_box(0), v_inst_191_, v_x_192_);
stack->m_num = v_res_194_;
}
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___boxed(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_x_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Std_Ric_isEmpty(v_00_u03b1_195_, v_inst_196_, v_x_197_);
lean_dec(v_x_197_);
lean_dec_ref(v_inst_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
uint8_t l_Std_Rio_isEmpty___redArg___lam__0(lean_object* v_inst_200_, lean_object* v_r_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_apply_2(v_inst_200_, v_a_202_, v_r_201_);
v___x_204_ = lean_unbox(v___x_203_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = 1;
return v___x_205_;
}
else
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
}
}
LEAN_EXPORT void l_Std_Rio_isEmpty___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_200_ = stack[0].m_obj;
lean_object* v_r_201_ = stack[1].m_obj;
lean_object* v_a_202_ = stack[2].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_Std_Rio_isEmpty___redArg___lam__0(v_inst_200_, v_r_201_, v_a_202_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___lam__0___boxed(lean_object* v_inst_208_, lean_object* v_r_209_, lean_object* v_a_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_Rio_isEmpty___redArg___lam__0(v_inst_208_, v_r_209_, v_a_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
uint8_t l_Std_Rio_isEmpty___redArg(lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_r_215_){
_start:
{
lean_object* v___f_216_; uint8_t v___x_217_; 
v___f_216_ = lean_alloc_closure((void*)(l_Std_Rio_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_216_, 0, v_inst_213_);
lean_closure_set(v___f_216_, 1, v_r_215_);
v___x_217_ = l_Option_decidableForallMem___redArg(v___f_216_, v_inst_214_);
return v___x_217_;
}
}
LEAN_EXPORT void l_Std_Rio_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_213_ = stack[0].m_obj;
lean_object* v_inst_214_ = stack[1].m_obj;
lean_object* v_r_215_ = stack[2].m_obj;
uint8_t v_res_218_;
v_res_218_ = l_Std_Rio_isEmpty___redArg(v_inst_213_, v_inst_214_, v_r_215_);
stack->m_num = v_res_218_;
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___boxed(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_r_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_Rio_isEmpty___redArg(v_inst_219_, v_inst_220_, v_r_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
uint8_t l_Std_Rio_isEmpty(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_r_229_){
_start:
{
lean_object* v___f_230_; uint8_t v___x_231_; 
v___f_230_ = lean_alloc_closure((void*)(l_Std_Rio_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_230_, 0, v_inst_226_);
lean_closure_set(v___f_230_, 1, v_r_229_);
v___x_231_ = l_Option_decidableForallMem___redArg(v___f_230_, v_inst_228_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Std_Rio_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_225_ = stack[1].m_obj;
lean_object* v_inst_226_ = stack[2].m_obj;
lean_object* v_inst_227_ = stack[3].m_obj;
lean_object* v_inst_228_ = stack[4].m_obj;
lean_object* v_r_229_ = stack[5].m_obj;
uint8_t v_res_232_;
v_res_232_ = l_Std_Rio_isEmpty(lean_box(0), v_inst_225_, v_inst_226_, v_inst_227_, v_inst_228_, v_r_229_);
stack->m_num = v_res_232_;
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___boxed(lean_object* v_00_u03b1_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_r_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_Rio_isEmpty(v_00_u03b1_233_, v_inst_234_, v_inst_235_, v_inst_236_, v_inst_237_, v_r_238_);
lean_dec_ref(v_inst_236_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
uint8_t l_Std_Rii_isEmpty___redArg(lean_object* v_inst_241_){
_start:
{
if (lean_obj_tag(v_inst_241_) == 0)
{
uint8_t v___x_242_; 
v___x_242_ = 1;
return v___x_242_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 0;
return v___x_243_;
}
}
}
LEAN_EXPORT void l_Std_Rii_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_241_ = stack[0].m_obj;
uint8_t v_res_244_;
v_res_244_ = l_Std_Rii_isEmpty___redArg(v_inst_241_);
stack->m_num = v_res_244_;
}
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___redArg___boxed(lean_object* v_inst_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_Rii_isEmpty___redArg(v_inst_245_);
lean_dec(v_inst_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
uint8_t l_Std_Rii_isEmpty(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_inst_249_) == 0)
{
uint8_t v___x_251_; 
v___x_251_ = 1;
return v___x_251_;
}
else
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
}
}
LEAN_EXPORT void l_Std_Rii_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_249_ = stack[1].m_obj;
lean_object* v_x_250_ = stack[2].m_obj;
uint8_t v_res_253_;
v_res_253_ = l_Std_Rii_isEmpty(lean_box(0), v_inst_249_, v_x_250_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___boxed(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_Rii_isEmpty(v_00_u03b1_254_, v_inst_255_, v_x_256_);
lean_dec(v_inst_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21));
v___x_305_ = l_String_toRawSubstring_x27(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44));
v___x_351_ = l_String_toRawSubstring_x27(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60));
v___x_385_ = l_String_toRawSubstring_x27(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66));
v___x_400_ = l_String_toRawSubstring_x27(v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_423_ = l_Lean_Syntax_isOfKind(v_x_419_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_box(1);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_a_421_);
return v___x_425_;
}
else
{
lean_object* v_quotContext_426_; lean_object* v_currMacroScope_427_; lean_object* v_ref_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_quotContext_426_ = lean_ctor_get(v_a_420_, 1);
v_currMacroScope_427_ = lean_ctor_get(v_a_420_, 2);
v_ref_428_ = lean_ctor_get(v_a_420_, 5);
v___x_429_ = 0;
v___x_430_ = l_Lean_SourceInfo_fromRef(v_ref_428_, v___x_429_);
v___x_431_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
v___x_432_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
lean_inc_n(v___x_430_, 50);
v___x_433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_430_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
v___x_434_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_435_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_436_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11));
v___x_437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_430_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
v___x_439_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
v___x_440_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
v___x_441_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_430_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
v___x_443_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
v___x_444_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22);
v___x_445_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27));
lean_inc_n(v_currMacroScope_427_, 4);
lean_inc_n(v_quotContext_426_, 4);
v___x_446_ = l_Lean_addMacroScope(v_quotContext_426_, v___x_445_, v_currMacroScope_427_);
v___x_447_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29));
v___x_448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_448_, 0, v___x_430_);
lean_ctor_set(v___x_448_, 1, v___x_444_);
lean_ctor_set(v___x_448_, 2, v___x_446_);
lean_ctor_set(v___x_448_, 3, v___x_447_);
v___x_449_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31));
v___x_450_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32));
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_430_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34));
v___x_453_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35));
v___x_454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_430_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_Syntax_node1(v___x_430_, v___x_452_, v___x_454_);
v___x_456_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36));
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_430_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_Syntax_node3(v___x_430_, v___x_449_, v___x_451_, v___x_455_, v___x_457_);
v___x_459_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38));
v___x_460_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40));
v___x_461_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41));
v___x_462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_430_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43));
v___x_464_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45);
v___x_465_ = lean_box(0);
v___x_466_ = l_Lean_addMacroScope(v_quotContext_426_, v___x_465_, v_currMacroScope_427_);
v___x_467_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52));
v___x_468_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_468_, 0, v___x_430_);
lean_ctor_set(v___x_468_, 1, v___x_464_);
lean_ctor_set(v___x_468_, 2, v___x_466_);
lean_ctor_set(v___x_468_, 3, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_430_, v___x_463_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node2(v___x_430_, v___x_460_, v___x_462_, v___x_469_);
v___x_471_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54));
v___x_472_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55));
v___x_473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_430_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57));
v___x_475_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58));
v___x_476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_430_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = l_Lean_Syntax_node1(v___x_430_, v___x_474_, v___x_476_);
v___x_478_ = l_Lean_Syntax_node1(v___x_430_, v___x_434_, v___x_477_);
v___x_479_ = l_Lean_Syntax_node1(v___x_430_, v___x_439_, v___x_478_);
v___x_480_ = l_Lean_Syntax_node1(v___x_430_, v___x_438_, v___x_479_);
v___x_481_ = l_Lean_Syntax_node2(v___x_430_, v___x_471_, v___x_473_, v___x_480_);
v___x_482_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59));
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_430_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_Syntax_node3(v___x_430_, v___x_459_, v___x_470_, v___x_481_, v___x_483_);
v___x_485_ = l_Lean_Syntax_node2(v___x_430_, v___x_434_, v___x_458_, v___x_484_);
lean_inc_n(v___x_485_, 2);
v___x_486_ = l_Lean_Syntax_node2(v___x_430_, v___x_443_, v___x_448_, v___x_485_);
lean_inc_ref_n(v___x_442_, 2);
v___x_487_ = l_Lean_Syntax_node2(v___x_430_, v___x_441_, v___x_442_, v___x_486_);
v___x_488_ = l_Lean_Syntax_node1(v___x_430_, v___x_434_, v___x_487_);
v___x_489_ = l_Lean_Syntax_node1(v___x_430_, v___x_439_, v___x_488_);
v___x_490_ = l_Lean_Syntax_node1(v___x_430_, v___x_438_, v___x_489_);
lean_inc_ref_n(v___x_437_, 3);
v___x_491_ = l_Lean_Syntax_node2(v___x_430_, v___x_435_, v___x_437_, v___x_490_);
v___x_492_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61);
v___x_493_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63));
v___x_494_ = l_Lean_addMacroScope(v_quotContext_426_, v___x_493_, v_currMacroScope_427_);
v___x_495_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65));
v___x_496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_496_, 0, v___x_430_);
lean_ctor_set(v___x_496_, 1, v___x_492_);
lean_ctor_set(v___x_496_, 2, v___x_494_);
lean_ctor_set(v___x_496_, 3, v___x_495_);
v___x_497_ = l_Lean_Syntax_node2(v___x_430_, v___x_443_, v___x_496_, v___x_485_);
v___x_498_ = l_Lean_Syntax_node2(v___x_430_, v___x_441_, v___x_442_, v___x_497_);
v___x_499_ = l_Lean_Syntax_node1(v___x_430_, v___x_434_, v___x_498_);
v___x_500_ = l_Lean_Syntax_node1(v___x_430_, v___x_439_, v___x_499_);
v___x_501_ = l_Lean_Syntax_node1(v___x_430_, v___x_438_, v___x_500_);
v___x_502_ = l_Lean_Syntax_node2(v___x_430_, v___x_435_, v___x_437_, v___x_501_);
v___x_503_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67);
v___x_504_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69));
v___x_505_ = l_Lean_addMacroScope(v_quotContext_426_, v___x_504_, v_currMacroScope_427_);
v___x_506_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71));
v___x_507_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_507_, 0, v___x_430_);
lean_ctor_set(v___x_507_, 1, v___x_503_);
lean_ctor_set(v___x_507_, 2, v___x_505_);
lean_ctor_set(v___x_507_, 3, v___x_506_);
v___x_508_ = l_Lean_Syntax_node2(v___x_430_, v___x_443_, v___x_507_, v___x_485_);
v___x_509_ = l_Lean_Syntax_node2(v___x_430_, v___x_441_, v___x_442_, v___x_508_);
v___x_510_ = l_Lean_Syntax_node1(v___x_430_, v___x_434_, v___x_509_);
v___x_511_ = l_Lean_Syntax_node1(v___x_430_, v___x_439_, v___x_510_);
v___x_512_ = l_Lean_Syntax_node1(v___x_430_, v___x_438_, v___x_511_);
v___x_513_ = l_Lean_Syntax_node2(v___x_430_, v___x_435_, v___x_437_, v___x_512_);
v___x_514_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72));
v___x_515_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73));
v___x_516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_430_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
v___x_517_ = l_Lean_Syntax_node1(v___x_430_, v___x_515_, v___x_516_);
v___x_518_ = l_Lean_Syntax_node1(v___x_430_, v___x_434_, v___x_517_);
v___x_519_ = l_Lean_Syntax_node1(v___x_430_, v___x_439_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node1(v___x_430_, v___x_438_, v___x_519_);
v___x_521_ = l_Lean_Syntax_node2(v___x_430_, v___x_435_, v___x_437_, v___x_520_);
v___x_522_ = l_Lean_Syntax_node4(v___x_430_, v___x_434_, v___x_491_, v___x_502_, v___x_513_, v___x_521_);
v___x_523_ = l_Lean_Syntax_node2(v___x_430_, v___x_432_, v___x_433_, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_a_421_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_525_, v_a_526_, v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_528_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
