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
LEAN_EXPORT uint8_t l_Std_Rci_isEmpty___redArg(){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___redArg___boxed(lean_object* v___dummy_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Std_Rci_isEmpty___redArg();
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_isEmpty(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_x_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_isEmpty___boxed(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Rci_isEmpty(v_00_u03b1_70_, v_inst_71_, v_x_72_);
lean_dec(v_x_72_);
lean_dec_ref(v_inst_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_isEmpty___redArg(lean_object* v_inst_75_, lean_object* v_r_76_){
_start:
{
lean_object* v_lower_77_; lean_object* v_upper_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_lower_77_ = lean_ctor_get(v_r_76_, 0);
lean_inc(v_lower_77_);
v_upper_78_ = lean_ctor_get(v_r_76_, 1);
lean_inc(v_upper_78_);
lean_dec_ref(v_r_76_);
v___x_79_ = lean_apply_2(v_inst_75_, v_lower_77_, v_upper_78_);
v___x_80_ = lean_unbox(v___x_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 1;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___redArg___boxed(lean_object* v_inst_83_, lean_object* v_r_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_Roc_isEmpty___redArg(v_inst_83_, v_r_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_isEmpty(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_r_91_){
_start:
{
lean_object* v_lower_92_; lean_object* v_upper_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_lower_92_ = lean_ctor_get(v_r_91_, 0);
lean_inc(v_lower_92_);
v_upper_93_ = lean_ctor_get(v_r_91_, 1);
lean_inc(v_upper_93_);
lean_dec_ref(v_r_91_);
v___x_94_ = lean_apply_2(v_inst_89_, v_lower_92_, v_upper_93_);
v___x_95_ = lean_unbox(v___x_94_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_isEmpty___boxed(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_r_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Roc_isEmpty(v_00_u03b1_98_, v_inst_99_, v_inst_100_, v_inst_101_, v_r_102_);
lean_dec_ref(v_inst_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty___redArg___lam__0(lean_object* v_inst_105_, lean_object* v_upper_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_apply_2(v_inst_105_, v_a_107_, v_upper_106_);
v___x_109_ = lean_unbox(v___x_108_);
if (v___x_109_ == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 1;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___lam__0___boxed(lean_object* v_inst_112_, lean_object* v_upper_113_, lean_object* v_a_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Std_Roo_isEmpty___redArg___lam__0(v_inst_112_, v_upper_113_, v_a_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty___redArg(lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_r_119_){
_start:
{
lean_object* v_succ_x3f_120_; lean_object* v_lower_121_; lean_object* v_upper_122_; lean_object* v___f_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_succ_x3f_120_ = lean_ctor_get(v_inst_118_, 0);
lean_inc_ref(v_succ_x3f_120_);
lean_dec_ref(v_inst_118_);
v_lower_121_ = lean_ctor_get(v_r_119_, 0);
lean_inc(v_lower_121_);
v_upper_122_ = lean_ctor_get(v_r_119_, 1);
lean_inc(v_upper_122_);
lean_dec_ref(v_r_119_);
v___f_123_ = lean_alloc_closure((void*)(l_Std_Roo_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_123_, 0, v_inst_117_);
lean_closure_set(v___f_123_, 1, v_upper_122_);
v___x_124_ = lean_apply_1(v_succ_x3f_120_, v_lower_121_);
v___x_125_ = l_Option_decidableForallMem___redArg(v___f_123_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___redArg___boxed(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_r_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Std_Roo_isEmpty___redArg(v_inst_126_, v_inst_127_, v_r_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_isEmpty(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_r_135_){
_start:
{
lean_object* v_succ_x3f_136_; lean_object* v_lower_137_; lean_object* v_upper_138_; lean_object* v___f_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_succ_x3f_136_ = lean_ctor_get(v_inst_134_, 0);
lean_inc_ref(v_succ_x3f_136_);
lean_dec_ref(v_inst_134_);
v_lower_137_ = lean_ctor_get(v_r_135_, 0);
lean_inc(v_lower_137_);
v_upper_138_ = lean_ctor_get(v_r_135_, 1);
lean_inc(v_upper_138_);
lean_dec_ref(v_r_135_);
v___f_139_ = lean_alloc_closure((void*)(l_Std_Roo_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_139_, 0, v_inst_133_);
lean_closure_set(v___f_139_, 1, v_upper_138_);
v___x_140_ = lean_apply_1(v_succ_x3f_136_, v_lower_137_);
v___x_141_ = l_Option_decidableForallMem___redArg(v___f_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_isEmpty___boxed(lean_object* v_00_u03b1_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_r_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Std_Roo_isEmpty(v_00_u03b1_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_r_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_isEmpty___redArg(lean_object* v_inst_149_, lean_object* v_r_150_){
_start:
{
lean_object* v_succ_x3f_151_; lean_object* v___x_152_; 
v_succ_x3f_151_ = lean_ctor_get(v_inst_149_, 0);
lean_inc_ref(v_succ_x3f_151_);
lean_dec_ref(v_inst_149_);
v___x_152_ = lean_apply_1(v_succ_x3f_151_, v_r_150_);
if (lean_obj_tag(v___x_152_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 1;
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
lean_dec_ref_known(v___x_152_, 1);
v___x_154_ = 0;
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___redArg___boxed(lean_object* v_inst_155_, lean_object* v_r_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_Roi_isEmpty___redArg(v_inst_155_, v_r_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_isEmpty(lean_object* v_00_u03b1_159_, lean_object* v_inst_160_, lean_object* v_r_161_){
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
LEAN_EXPORT lean_object* l_Std_Roi_isEmpty___boxed(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_r_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_Roi_isEmpty(v_00_u03b1_166_, v_inst_167_, v_r_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_isEmpty___redArg(){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___redArg___boxed(lean_object* v___dummy_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_Ric_isEmpty___redArg();
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_isEmpty(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_x_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_isEmpty___boxed(lean_object* v_00_u03b1_180_, lean_object* v_inst_181_, lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_Ric_isEmpty(v_00_u03b1_180_, v_inst_181_, v_x_182_);
lean_dec(v_x_182_);
lean_dec_ref(v_inst_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty___redArg___lam__0(lean_object* v_inst_185_, lean_object* v_r_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_apply_2(v_inst_185_, v_a_187_, v_r_186_);
v___x_189_ = lean_unbox(v___x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
v___x_190_ = 1;
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___lam__0___boxed(lean_object* v_inst_192_, lean_object* v_r_193_, lean_object* v_a_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_Rio_isEmpty___redArg___lam__0(v_inst_192_, v_r_193_, v_a_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty___redArg(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_r_199_){
_start:
{
lean_object* v___f_200_; uint8_t v___x_201_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_Rio_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_200_, 0, v_inst_197_);
lean_closure_set(v___f_200_, 1, v_r_199_);
v___x_201_ = l_Option_decidableForallMem___redArg(v___f_200_, v_inst_198_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___redArg___boxed(lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_r_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_Rio_isEmpty___redArg(v_inst_202_, v_inst_203_, v_r_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_isEmpty(lean_object* v_00_u03b1_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_r_212_){
_start:
{
lean_object* v___f_213_; uint8_t v___x_214_; 
v___f_213_ = lean_alloc_closure((void*)(l_Std_Rio_isEmpty___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_213_, 0, v_inst_209_);
lean_closure_set(v___f_213_, 1, v_r_212_);
v___x_214_ = l_Option_decidableForallMem___redArg(v___f_213_, v_inst_211_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_isEmpty___boxed(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_r_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Std_Rio_isEmpty(v_00_u03b1_215_, v_inst_216_, v_inst_217_, v_inst_218_, v_inst_219_, v_r_220_);
lean_dec_ref(v_inst_218_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_isEmpty___redArg(lean_object* v_inst_223_){
_start:
{
if (lean_obj_tag(v_inst_223_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 1;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 0;
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___redArg___boxed(lean_object* v_inst_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_Rii_isEmpty___redArg(v_inst_226_);
lean_dec(v_inst_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_isEmpty(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_inst_230_) == 0)
{
uint8_t v___x_232_; 
v___x_232_ = 1;
return v___x_232_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_isEmpty___boxed(lean_object* v_00_u03b1_234_, lean_object* v_inst_235_, lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_Rii_isEmpty(v_00_u03b1_234_, v_inst_235_, v_x_236_);
lean_dec(v_inst_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21));
v___x_285_ = l_String_toRawSubstring_x27(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44));
v___x_331_ = l_String_toRawSubstring_x27(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60));
v___x_365_ = l_String_toRawSubstring_x27(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66));
v___x_380_ = l_String_toRawSubstring_x27(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_403_ = l_Lean_Syntax_isOfKind(v_x_399_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_box(1);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_a_401_);
return v___x_405_;
}
else
{
lean_object* v_quotContext_406_; lean_object* v_currMacroScope_407_; lean_object* v_ref_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_quotContext_406_ = lean_ctor_get(v_a_400_, 1);
v_currMacroScope_407_ = lean_ctor_get(v_a_400_, 2);
v_ref_408_ = lean_ctor_get(v_a_400_, 5);
v___x_409_ = 0;
v___x_410_ = l_Lean_SourceInfo_fromRef(v_ref_408_, v___x_409_);
v___x_411_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
v___x_412_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
lean_inc_n(v___x_410_, 50);
v___x_413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_410_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
v___x_414_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_415_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_416_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11));
v___x_417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_410_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
v___x_419_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
v___x_420_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
v___x_421_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_410_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
v___x_423_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
v___x_424_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22);
v___x_425_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27));
lean_inc_n(v_currMacroScope_407_, 4);
lean_inc_n(v_quotContext_406_, 4);
v___x_426_ = l_Lean_addMacroScope(v_quotContext_406_, v___x_425_, v_currMacroScope_407_);
v___x_427_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29));
v___x_428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_428_, 0, v___x_410_);
lean_ctor_set(v___x_428_, 1, v___x_424_);
lean_ctor_set(v___x_428_, 2, v___x_426_);
lean_ctor_set(v___x_428_, 3, v___x_427_);
v___x_429_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31));
v___x_430_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32));
v___x_431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_410_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34));
v___x_433_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35));
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_410_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_Syntax_node1(v___x_410_, v___x_432_, v___x_434_);
v___x_436_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36));
v___x_437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_410_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_Syntax_node3(v___x_410_, v___x_429_, v___x_431_, v___x_435_, v___x_437_);
v___x_439_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38));
v___x_440_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40));
v___x_441_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41));
v___x_442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_410_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43));
v___x_444_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45);
v___x_445_ = lean_box(0);
v___x_446_ = l_Lean_addMacroScope(v_quotContext_406_, v___x_445_, v_currMacroScope_407_);
v___x_447_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52));
v___x_448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_448_, 0, v___x_410_);
lean_ctor_set(v___x_448_, 1, v___x_444_);
lean_ctor_set(v___x_448_, 2, v___x_446_);
lean_ctor_set(v___x_448_, 3, v___x_447_);
v___x_449_ = l_Lean_Syntax_node1(v___x_410_, v___x_443_, v___x_448_);
v___x_450_ = l_Lean_Syntax_node2(v___x_410_, v___x_440_, v___x_442_, v___x_449_);
v___x_451_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54));
v___x_452_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55));
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_410_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57));
v___x_455_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58));
v___x_456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_410_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_Syntax_node1(v___x_410_, v___x_454_, v___x_456_);
v___x_458_ = l_Lean_Syntax_node1(v___x_410_, v___x_414_, v___x_457_);
v___x_459_ = l_Lean_Syntax_node1(v___x_410_, v___x_419_, v___x_458_);
v___x_460_ = l_Lean_Syntax_node1(v___x_410_, v___x_418_, v___x_459_);
v___x_461_ = l_Lean_Syntax_node2(v___x_410_, v___x_451_, v___x_453_, v___x_460_);
v___x_462_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59));
v___x_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_410_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_Syntax_node3(v___x_410_, v___x_439_, v___x_450_, v___x_461_, v___x_463_);
v___x_465_ = l_Lean_Syntax_node2(v___x_410_, v___x_414_, v___x_438_, v___x_464_);
lean_inc_n(v___x_465_, 2);
v___x_466_ = l_Lean_Syntax_node2(v___x_410_, v___x_423_, v___x_428_, v___x_465_);
lean_inc_ref_n(v___x_422_, 2);
v___x_467_ = l_Lean_Syntax_node2(v___x_410_, v___x_421_, v___x_422_, v___x_466_);
v___x_468_ = l_Lean_Syntax_node1(v___x_410_, v___x_414_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_410_, v___x_419_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v___x_410_, v___x_418_, v___x_469_);
lean_inc_ref_n(v___x_417_, 3);
v___x_471_ = l_Lean_Syntax_node2(v___x_410_, v___x_415_, v___x_417_, v___x_470_);
v___x_472_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61);
v___x_473_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63));
v___x_474_ = l_Lean_addMacroScope(v_quotContext_406_, v___x_473_, v_currMacroScope_407_);
v___x_475_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65));
v___x_476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_476_, 0, v___x_410_);
lean_ctor_set(v___x_476_, 1, v___x_472_);
lean_ctor_set(v___x_476_, 2, v___x_474_);
lean_ctor_set(v___x_476_, 3, v___x_475_);
v___x_477_ = l_Lean_Syntax_node2(v___x_410_, v___x_423_, v___x_476_, v___x_465_);
v___x_478_ = l_Lean_Syntax_node2(v___x_410_, v___x_421_, v___x_422_, v___x_477_);
v___x_479_ = l_Lean_Syntax_node1(v___x_410_, v___x_414_, v___x_478_);
v___x_480_ = l_Lean_Syntax_node1(v___x_410_, v___x_419_, v___x_479_);
v___x_481_ = l_Lean_Syntax_node1(v___x_410_, v___x_418_, v___x_480_);
v___x_482_ = l_Lean_Syntax_node2(v___x_410_, v___x_415_, v___x_417_, v___x_481_);
v___x_483_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67, &l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67);
v___x_484_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69));
v___x_485_ = l_Lean_addMacroScope(v_quotContext_406_, v___x_484_, v_currMacroScope_407_);
v___x_486_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71));
v___x_487_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_487_, 0, v___x_410_);
lean_ctor_set(v___x_487_, 1, v___x_483_);
lean_ctor_set(v___x_487_, 2, v___x_485_);
lean_ctor_set(v___x_487_, 3, v___x_486_);
v___x_488_ = l_Lean_Syntax_node2(v___x_410_, v___x_423_, v___x_487_, v___x_465_);
v___x_489_ = l_Lean_Syntax_node2(v___x_410_, v___x_421_, v___x_422_, v___x_488_);
v___x_490_ = l_Lean_Syntax_node1(v___x_410_, v___x_414_, v___x_489_);
v___x_491_ = l_Lean_Syntax_node1(v___x_410_, v___x_419_, v___x_490_);
v___x_492_ = l_Lean_Syntax_node1(v___x_410_, v___x_418_, v___x_491_);
v___x_493_ = l_Lean_Syntax_node2(v___x_410_, v___x_415_, v___x_417_, v___x_492_);
v___x_494_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72));
v___x_495_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73));
v___x_496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_410_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
v___x_497_ = l_Lean_Syntax_node1(v___x_410_, v___x_495_, v___x_496_);
v___x_498_ = l_Lean_Syntax_node1(v___x_410_, v___x_414_, v___x_497_);
v___x_499_ = l_Lean_Syntax_node1(v___x_410_, v___x_419_, v___x_498_);
v___x_500_ = l_Lean_Syntax_node1(v___x_410_, v___x_418_, v___x_499_);
v___x_501_ = l_Lean_Syntax_node2(v___x_410_, v___x_415_, v___x_417_, v___x_500_);
v___x_502_ = l_Lean_Syntax_node4(v___x_410_, v___x_414_, v___x_471_, v___x_482_, v___x_493_, v___x_501_);
v___x_503_ = l_Lean_Syntax_node2(v___x_410_, v___x_412_, v___x_413_, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_a_401_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object* v_x_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_505_, v_a_506_, v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_508_;
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
