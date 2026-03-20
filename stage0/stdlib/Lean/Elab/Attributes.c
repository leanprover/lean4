// Lean compiler output
// Module: Lean.Elab.Attributes
// Imports: public import Lean.Elab.Util public import Lean.Compiler.InitAttr import Lean.Parser.Term public import Init.Data.Format.Macro
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
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
extern lean_object* l_Lean_regularInitAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static const lean_ctor_object l_Lean_Elab_instInhabitedAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_instInhabitedAttribute_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedAttribute_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedAttribute_default = (const lean_object*)&l_Lean_Elab_instInhabitedAttribute_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedAttribute = (const lean_object*)&l_Lean_Elab_instInhabitedAttribute_default___closed__0_value;
static const lean_string_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_instToFormatAttribute___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_instToFormatAttribute___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__3;
static const lean_ctor_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "local "};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_instToFormatAttribute___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scoped "};
static const lean_object* l_Lean_Elab_instToFormatAttribute___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatAttribute___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_instToFormatAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToFormatAttribute___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToFormatAttribute___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToFormatAttribute = (const lean_object*)&l_Lean_Elab_instToFormatAttribute___closed__0_value;
static const lean_string_object l_Lean_Elab_toAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_toAttributeKind___closed__0 = (const lean_object*)&l_Lean_Elab_toAttributeKind___closed__0_value;
static const lean_string_object l_Lean_Elab_toAttributeKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_toAttributeKind___closed__1 = (const lean_object*)&l_Lean_Elab_toAttributeKind___closed__1_value;
static const lean_string_object l_Lean_Elab_toAttributeKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_toAttributeKind___closed__2 = (const lean_object*)&l_Lean_Elab_toAttributeKind___closed__2_value;
static const lean_string_object l_Lean_Elab_toAttributeKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_Elab_toAttributeKind___closed__3 = (const lean_object*)&l_Lean_Elab_toAttributeKind___closed__3_value;
static const lean_ctor_object l_Lean_Elab_toAttributeKind___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_toAttributeKind___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_toAttributeKind___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_toAttributeKind___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_toAttributeKind___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_toAttributeKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_toAttributeKind___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(199, 36, 31, 135, 78, 131, 139, 152)}};
static const lean_object* l_Lean_Elab_toAttributeKind___closed__4 = (const lean_object*)&l_Lean_Elab_toAttributeKind___closed__4_value;
static const lean_string_object l_Lean_Elab_toAttributeKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Scoped attributes must be used inside namespaces"};
static const lean_object* l_Lean_Elab_toAttributeKind___closed__5 = (const lean_object*)&l_Lean_Elab_toAttributeKind___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_toAttributeKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkAttrKindGlobal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__0 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__0_value;
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__1 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__1_value;
static const lean_array_object l_Lean_Elab_mkAttrKindGlobal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__2 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__2_value;
static const lean_string_object l_Lean_Elab_mkAttrKindGlobal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__3 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__3_value;
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__4 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__4_value;
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__4_value),((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__2_value)}};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__5 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__5_value;
static const lean_array_object l_Lean_Elab_mkAttrKindGlobal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__5_value)}};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__6 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__6_value;
static const lean_ctor_object l_Lean_Elab_mkAttrKindGlobal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__1_value),((lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__6_value)}};
static const lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__7 = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_mkAttrKindGlobal = (const lean_object*)&l_Lean_Elab_mkAttrKindGlobal___closed__7_value;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]`"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__0_value;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___closed__1 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__1_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__2_value;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unknown attribute"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___closed__3 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__10___closed__3_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_elabAttr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_elabAttr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabAttr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__6(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_elabAttrs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_elabAttrs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttrs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__2(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__0));
v___x_10_ = lean_string_length(v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__3(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l_Lean_Elab_instToFormatAttribute___lam__0___closed__2, &l_Lean_Elab_instToFormatAttribute___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__2);
v___x_12_ = lean_nat_to_int(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatAttribute___lam__0(lean_object* v_attr_20_){
_start:
{
uint8_t v_kind_21_; lean_object* v_name_22_; lean_object* v_stx_23_; lean_object* v___y_25_; 
v_kind_21_ = lean_ctor_get_uint8(v_attr_20_, sizeof(void*)*2);
v_name_22_ = lean_ctor_get(v_attr_20_, 0);
lean_inc(v_name_22_);
v_stx_23_ = lean_ctor_get(v_attr_20_, 1);
lean_inc(v_stx_23_);
lean_dec_ref(v_attr_20_);
switch(v_kind_21_)
{
case 0:
{
lean_object* v___x_47_; 
v___x_47_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__6));
v___y_25_ = v___x_47_;
goto v___jp_24_;
}
case 1:
{
lean_object* v___x_48_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__7));
v___y_25_ = v___x_48_;
goto v___jp_24_;
}
default: 
{
lean_object* v___x_49_; 
v___x_49_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__8));
v___y_25_ = v___x_49_;
goto v___jp_24_;
}
}
v___jp_24_:
{
lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; lean_object* v___x_46_; 
v___x_26_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_26_, 0, v___y_25_);
v___x_27_ = 1;
v___x_28_ = l_Lean_Name_toString(v_name_22_, v___x_27_);
v___x_29_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
v___x_30_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_26_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = lean_box(0);
v___x_32_ = 0;
v___x_33_ = l_Lean_Syntax_formatStx(v_stx_23_, v___x_31_, v___x_32_);
v___x_34_ = l_Std_Format_defWidth;
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = l_Std_Format_pretty(v___x_33_, v___x_34_, v___x_35_, v___x_35_);
v___x_37_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_30_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_obj_once(&l_Lean_Elab_instToFormatAttribute___lam__0___closed__3, &l_Lean_Elab_instToFormatAttribute___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__3);
v___x_40_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__4));
v___x_41_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v___x_38_);
v___x_42_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__5));
v___x_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_39_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = 0;
v___x_46_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*1, v___x_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_toAttributeKind(lean_object* v_attrKindStx_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = l_Lean_Syntax_getArg(v_attrKindStx_62_, v___x_65_);
v___x_67_ = l_Lean_Syntax_isNone(v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_68_ = l_Lean_Syntax_getArg(v___x_66_, v___x_65_);
lean_dec(v___x_66_);
v___x_69_ = l_Lean_Syntax_getKind(v___x_68_);
v___x_70_ = ((lean_object*)(l_Lean_Elab_toAttributeKind___closed__4));
v___x_71_ = lean_name_eq(v___x_69_, v___x_70_);
lean_dec(v___x_69_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v_a_63_);
v___x_72_ = 1;
v___x_73_ = lean_box(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_a_64_);
return v___x_74_;
}
else
{
lean_object* v___x_75_; 
lean_inc_ref(v_a_63_);
v___x_75_ = l_Lean_Macro_getCurrNamespace(v_a_63_, v_a_64_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_93_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_a_77_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_93_ == 0)
{
v___x_79_ = v___x_75_;
v_isShared_80_ = v_isSharedCheck_93_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_93_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_Name_isAnonymous(v_a_76_);
lean_dec(v_a_76_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
lean_dec_ref(v_a_63_);
v___x_82_ = 2;
v___x_83_ = lean_box(v___x_82_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_83_);
v___x_85_ = v___x_79_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_a_77_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
else
{
lean_object* v_ref_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v_ref_87_ = lean_ctor_get(v_a_63_, 5);
lean_inc(v_ref_87_);
lean_dec_ref(v_a_63_);
v___x_88_ = ((lean_object*)(l_Lean_Elab_toAttributeKind___closed__5));
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_ref_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 1);
lean_ctor_set(v___x_79_, 0, v___x_89_);
v___x_91_ = v___x_79_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_a_77_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_a_63_);
v_a_94_ = lean_ctor_get(v___x_75_, 0);
v_a_95_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_75_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_inc(v_a_94_);
lean_dec(v___x_75_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
else
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v___x_66_);
lean_dec_ref(v_a_63_);
v___x_103_ = 0;
v___x_104_ = lean_box(v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_64_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object* v_attrKindStx_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Elab_toAttributeKind(v_attrKindStx_106_, v_a_107_, v_a_108_);
lean_dec(v_attrKindStx_106_);
return v_res_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___redArg___lam__0(lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__0___closed__1));
v___x_142_ = lean_name_eq(v_k_140_, v___x_141_);
if (v___x_142_ == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 1;
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__0___boxed(lean_object* v_k_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Lean_Elab_elabAttr___redArg___lam__0(v_k_145_);
lean_dec(v_k_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__1(uint8_t v_attrKind_148_, lean_object* v_attrName_149_, lean_object* v_attr_150_, lean_object* v_toPure_151_, lean_object* v_____r_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_153_, 0, v_attrName_149_);
lean_ctor_set(v___x_153_, 1, v_attr_150_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*2, v_attrKind_148_);
v___x_154_ = lean_apply_2(v_toPure_151_, lean_box(0), v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__1___boxed(lean_object* v_attrKind_155_, lean_object* v_attrName_156_, lean_object* v_attr_157_, lean_object* v_toPure_158_, lean_object* v_____r_159_){
_start:
{
uint8_t v_attrKind_boxed_160_; lean_object* v_res_161_; 
v_attrKind_boxed_160_ = lean_unbox(v_attrKind_155_);
v_res_161_ = l_Lean_Elab_elabAttr___redArg___lam__1(v_attrKind_boxed_160_, v_attrName_156_, v_attr_157_, v_toPure_158_, v_____r_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__2(lean_object* v___f_162_, lean_object* v_____r_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_apply_1(v___f_162_, v_____r_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object* v_a_165_, lean_object* v___x_166_, lean_object* v___f_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_toBind_174_, lean_object* v___f_175_, lean_object* v_____do__lift_176_){
_start:
{
lean_object* v_toAttributeImplCore_177_; lean_object* v_ref_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toAttributeImplCore_177_ = lean_ctor_get(v_a_165_, 0);
lean_inc_ref(v_toAttributeImplCore_177_);
lean_dec_ref(v_a_165_);
v_ref_178_ = lean_ctor_get(v_toAttributeImplCore_177_, 0);
lean_inc(v_ref_178_);
lean_dec_ref(v_toAttributeImplCore_177_);
v___x_179_ = l_Lean_regularInitAttr;
lean_inc(v_ref_178_);
v___x_180_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_166_, v___x_179_, v_____do__lift_176_, v_ref_178_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_ref_178_);
lean_dec(v___f_175_);
lean_dec(v_toBind_174_);
lean_dec(v_inst_173_);
lean_dec(v_inst_172_);
lean_dec_ref(v_inst_171_);
lean_dec_ref(v_inst_170_);
lean_dec_ref(v_inst_169_);
lean_dec_ref(v_inst_168_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_1(v___f_167_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_toMonadRef_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec_ref(v___x_180_);
lean_dec(v___f_167_);
v_toMonadRef_183_ = lean_ctor_get(v_inst_168_, 1);
lean_inc_ref(v_toMonadRef_183_);
lean_dec_ref(v_inst_168_);
v___x_184_ = 1;
v___x_185_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_169_, v_inst_170_, v_inst_171_, v_inst_172_, v_toMonadRef_183_, v_inst_173_, v_ref_178_, v___x_184_);
v___x_186_ = lean_apply_4(v_toBind_174_, lean_box(0), lean_box(0), v___x_185_, v___f_175_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object* v_attrName_187_, lean_object* v___x_188_, lean_object* v___f_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_toBind_196_, lean_object* v___f_197_, lean_object* v_getEnv_198_, lean_object* v_____do__lift_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_getAttributeImpl(v_____do__lift_199_, v_attrName_187_);
if (lean_obj_tag(v___x_200_) == 1)
{
lean_object* v_a_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref(v___x_200_);
lean_inc(v_toBind_196_);
v___f_202_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__3), 12, 11);
lean_closure_set(v___f_202_, 0, v_a_201_);
lean_closure_set(v___f_202_, 1, v___x_188_);
lean_closure_set(v___f_202_, 2, v___f_189_);
lean_closure_set(v___f_202_, 3, v_inst_190_);
lean_closure_set(v___f_202_, 4, v_inst_191_);
lean_closure_set(v___f_202_, 5, v_inst_192_);
lean_closure_set(v___f_202_, 6, v_inst_193_);
lean_closure_set(v___f_202_, 7, v_inst_194_);
lean_closure_set(v___f_202_, 8, v_inst_195_);
lean_closure_set(v___f_202_, 9, v_toBind_196_);
lean_closure_set(v___f_202_, 10, v___f_197_);
v___x_203_ = lean_apply_4(v_toBind_196_, lean_box(0), lean_box(0), v_getEnv_198_, v___f_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref(v___x_200_);
lean_dec(v_getEnv_198_);
lean_dec(v___f_197_);
lean_dec(v_toBind_196_);
lean_dec(v_inst_195_);
lean_dec(v_inst_194_);
lean_dec_ref(v_inst_193_);
lean_dec_ref(v_inst_192_);
lean_dec_ref(v_inst_191_);
lean_dec_ref(v_inst_190_);
lean_dec(v___x_188_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_1(v___f_189_, v___x_204_);
return v___x_205_;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__0));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__2));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object* v_attrName_212_, lean_object* v_toBind_213_, lean_object* v_getEnv_214_, lean_object* v___f_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_____do__lift_218_){
_start:
{
lean_object* v___x_219_; 
lean_inc(v_attrName_212_);
v___x_219_ = l_Lean_getAttributeImpl(v_____do__lift_218_, v_attrName_212_);
if (lean_obj_tag(v___x_219_) == 1)
{
lean_object* v___x_220_; 
lean_dec_ref(v___x_219_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_inst_216_);
lean_dec(v_attrName_212_);
v___x_220_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v_getEnv_214_, v___f_215_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v___x_219_);
lean_dec(v___f_215_);
lean_dec(v_getEnv_214_);
lean_dec(v_toBind_213_);
v___x_221_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1);
v___x_222_ = l_Lean_MessageData_ofName(v_attrName_212_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = l_Lean_throwError___redArg(v_inst_216_, v_inst_217_, v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object* v_inst_227_, uint8_t v_attrKind_228_, lean_object* v_attr_229_, lean_object* v_toPure_230_, lean_object* v___x_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_toBind_237_, lean_object* v_attrName_238_){
_start:
{
lean_object* v_getEnv_239_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; 
v_getEnv_239_ = lean_ctor_get(v_inst_227_, 0);
lean_inc(v_getEnv_239_);
v___x_240_ = lean_box(v_attrKind_228_);
lean_inc(v_attrName_238_);
v___f_241_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_241_, 0, v___x_240_);
lean_closure_set(v___f_241_, 1, v_attrName_238_);
lean_closure_set(v___f_241_, 2, v_attr_229_);
lean_closure_set(v___f_241_, 3, v_toPure_230_);
lean_inc_ref(v___f_241_);
v___f_242_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_242_, 0, v___f_241_);
lean_inc(v_getEnv_239_);
lean_inc(v_toBind_237_);
lean_inc_ref(v_inst_233_);
lean_inc_ref(v_inst_232_);
lean_inc(v_attrName_238_);
v___f_243_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__4), 13, 12);
lean_closure_set(v___f_243_, 0, v_attrName_238_);
lean_closure_set(v___f_243_, 1, v___x_231_);
lean_closure_set(v___f_243_, 2, v___f_241_);
lean_closure_set(v___f_243_, 3, v_inst_232_);
lean_closure_set(v___f_243_, 4, v_inst_233_);
lean_closure_set(v___f_243_, 5, v_inst_227_);
lean_closure_set(v___f_243_, 6, v_inst_234_);
lean_closure_set(v___f_243_, 7, v_inst_235_);
lean_closure_set(v___f_243_, 8, v_inst_236_);
lean_closure_set(v___f_243_, 9, v_toBind_237_);
lean_closure_set(v___f_243_, 10, v___f_242_);
lean_closure_set(v___f_243_, 11, v_getEnv_239_);
lean_inc(v_getEnv_239_);
lean_inc(v_toBind_237_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__5), 7, 6);
lean_closure_set(v___f_244_, 0, v_attrName_238_);
lean_closure_set(v___f_244_, 1, v_toBind_237_);
lean_closure_set(v___f_244_, 2, v_getEnv_239_);
lean_closure_set(v___f_244_, 3, v___f_243_);
lean_closure_set(v___f_244_, 4, v_inst_233_);
lean_closure_set(v___f_244_, 5, v_inst_232_);
v___x_245_ = lean_apply_4(v_toBind_237_, lean_box(0), lean_box(0), v_getEnv_239_, v___f_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6___boxed(lean_object* v_inst_246_, lean_object* v_attrKind_247_, lean_object* v_attr_248_, lean_object* v_toPure_249_, lean_object* v___x_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_toBind_256_, lean_object* v_attrName_257_){
_start:
{
uint8_t v_attrKind_boxed_258_; lean_object* v_res_259_; 
v_attrKind_boxed_258_ = lean_unbox(v_attrKind_247_);
v_res_259_ = l_Lean_Elab_elabAttr___redArg___lam__6(v_inst_246_, v_attrKind_boxed_258_, v_attr_248_, v_toPure_249_, v___x_250_, v_inst_251_, v_inst_252_, v_inst_253_, v_inst_254_, v_inst_255_, v_toBind_256_, v_attrName_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object* v___f_260_, lean_object* v_attrName_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_apply_1(v___f_260_, v_attrName_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__10___closed__4(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__10___closed__3));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object* v_inst_273_, uint8_t v_attrKind_274_, lean_object* v_toPure_275_, lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_toBind_282_, lean_object* v___x_283_, lean_object* v_attr_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_285_ = lean_box(v_attrKind_274_);
lean_inc(v_toBind_282_);
lean_inc_ref(v_inst_278_);
lean_inc_ref(v_inst_277_);
lean_inc(v_toPure_275_);
lean_inc(v_attr_284_);
v___f_286_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__6___boxed), 12, 11);
lean_closure_set(v___f_286_, 0, v_inst_273_);
lean_closure_set(v___f_286_, 1, v___x_285_);
lean_closure_set(v___f_286_, 2, v_attr_284_);
lean_closure_set(v___f_286_, 3, v_toPure_275_);
lean_closure_set(v___f_286_, 4, v___x_276_);
lean_closure_set(v___f_286_, 5, v_inst_277_);
lean_closure_set(v___f_286_, 6, v_inst_278_);
lean_closure_set(v___f_286_, 7, v_inst_279_);
lean_closure_set(v___f_286_, 8, v_inst_280_);
lean_closure_set(v___f_286_, 9, v_inst_281_);
lean_closure_set(v___f_286_, 10, v_toBind_282_);
lean_inc(v_attr_284_);
v___x_287_ = l_Lean_Syntax_getKind(v_attr_284_);
v___x_288_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__10___closed__2));
v___x_289_ = lean_name_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
if (lean_obj_tag(v___x_287_) == 1)
{
lean_object* v_str_290_; lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_attr_284_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
v_str_290_ = lean_ctor_get(v___x_287_, 1);
lean_inc_ref(v_str_290_);
lean_dec_ref(v___x_287_);
v___f_291_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 2, 1);
lean_closure_set(v___f_291_, 0, v___f_286_);
v___x_292_ = lean_box(0);
v___x_293_ = l_Lean_Name_str___override(v___x_292_, v_str_290_);
v___x_294_ = lean_apply_2(v_toPure_275_, lean_box(0), v___x_293_);
v___x_295_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_294_, v___f_291_);
return v___x_295_;
}
else
{
lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___x_287_);
lean_dec(v_toPure_275_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 2, 1);
lean_closure_set(v___f_296_, 0, v___f_286_);
v___x_297_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__10___closed__4, &l_Lean_Elab_elabAttr___redArg___lam__10___closed__4_once, _init_l_Lean_Elab_elabAttr___redArg___lam__10___closed__4);
v___x_298_ = l_Lean_throwErrorAt___redArg(v_inst_278_, v_inst_277_, v_attr_284_, v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_298_, v___f_296_);
return v___x_299_;
}
}
else
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_287_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 2, 1);
lean_closure_set(v___f_300_, 0, v___f_286_);
v___x_301_ = l_Lean_Syntax_getArg(v_attr_284_, v___x_283_);
lean_dec(v_attr_284_);
v___x_302_ = l_Lean_Syntax_getId(v___x_301_);
lean_dec(v___x_301_);
v___x_303_ = lean_erase_macro_scopes(v___x_302_);
v___x_304_ = lean_apply_2(v_toPure_275_, lean_box(0), v___x_303_);
v___x_305_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_304_, v___f_300_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10___boxed(lean_object* v_inst_306_, lean_object* v_attrKind_307_, lean_object* v_toPure_308_, lean_object* v___x_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_toBind_315_, lean_object* v___x_316_, lean_object* v_attr_317_){
_start:
{
uint8_t v_attrKind_boxed_318_; lean_object* v_res_319_; 
v_attrKind_boxed_318_ = lean_unbox(v_attrKind_307_);
v_res_319_ = l_Lean_Elab_elabAttr___redArg___lam__10(v_inst_306_, v_attrKind_boxed_318_, v_toPure_308_, v___x_309_, v_inst_310_, v_inst_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_toBind_315_, v___x_316_, v_attr_317_);
lean_dec(v___x_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object* v_inst_320_, lean_object* v_toPure_321_, lean_object* v___x_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_toBind_328_, lean_object* v___x_329_, lean_object* v_attrInstance_330_, lean_object* v___f_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, uint8_t v_attrKind_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v_attr_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_336_ = lean_box(v_attrKind_335_);
lean_inc(v_toBind_328_);
lean_inc(v_inst_327_);
lean_inc(v_inst_326_);
lean_inc_ref(v_inst_325_);
lean_inc_ref(v_inst_324_);
lean_inc_ref(v_inst_323_);
lean_inc_ref(v_inst_320_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_337_, 0, v_inst_320_);
lean_closure_set(v___f_337_, 1, v___x_336_);
lean_closure_set(v___f_337_, 2, v_toPure_321_);
lean_closure_set(v___f_337_, 3, v___x_322_);
lean_closure_set(v___f_337_, 4, v_inst_323_);
lean_closure_set(v___f_337_, 5, v_inst_324_);
lean_closure_set(v___f_337_, 6, v_inst_325_);
lean_closure_set(v___f_337_, 7, v_inst_326_);
lean_closure_set(v___f_337_, 8, v_inst_327_);
lean_closure_set(v___f_337_, 9, v_toBind_328_);
lean_closure_set(v___f_337_, 10, v___x_329_);
v___x_338_ = lean_unsigned_to_nat(1u);
v_attr_339_ = l_Lean_Syntax_getArg(v_attrInstance_330_, v___x_338_);
v___x_340_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_340_, 0, v_attr_339_);
lean_closure_set(v___x_340_, 1, v___f_331_);
v___x_341_ = l_Lean_Elab_liftMacroM___redArg(v_inst_324_, v_inst_332_, v_inst_320_, v_inst_333_, v_inst_323_, v_inst_334_, v_inst_325_, v_inst_326_, v_inst_327_, v___x_340_);
v___x_342_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_341_, v___f_337_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___boxed(lean_object* v_inst_343_, lean_object* v_toPure_344_, lean_object* v___x_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_toBind_351_, lean_object* v___x_352_, lean_object* v_attrInstance_353_, lean_object* v___f_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_attrKind_358_){
_start:
{
uint8_t v_attrKind_boxed_359_; lean_object* v_res_360_; 
v_attrKind_boxed_359_ = lean_unbox(v_attrKind_358_);
v_res_360_ = l_Lean_Elab_elabAttr___redArg___lam__8(v_inst_343_, v_toPure_344_, v___x_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_toBind_351_, v___x_352_, v_attrInstance_353_, v___f_354_, v_inst_355_, v_inst_356_, v_inst_357_, v_attrKind_boxed_359_);
lean_dec(v_attrInstance_353_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg(lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_attrInstance_372_){
_start:
{
lean_object* v_toApplicative_373_; lean_object* v_toBind_374_; lean_object* v_toPure_375_; lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; 
v_toApplicative_373_ = lean_ctor_get(v_inst_362_, 0);
v_toBind_374_ = lean_ctor_get(v_inst_362_, 1);
v_toPure_375_ = lean_ctor_get(v_toApplicative_373_, 1);
v___f_376_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___closed__0));
v___x_377_ = lean_box(0);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = l_Lean_Syntax_getArg(v_attrInstance_372_, v___x_378_);
v___x_380_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_380_, 0, v___x_379_);
lean_inc(v_inst_370_);
lean_inc(v_inst_369_);
lean_inc_ref(v_inst_368_);
lean_inc_ref(v_inst_364_);
lean_inc_ref(v_inst_365_);
lean_inc_ref(v_inst_367_);
lean_inc_ref(v_inst_363_);
lean_inc_ref(v_inst_366_);
lean_inc_ref(v_inst_362_);
v___x_381_ = l_Lean_Elab_liftMacroM___redArg(v_inst_362_, v_inst_366_, v_inst_363_, v_inst_367_, v_inst_365_, v_inst_364_, v_inst_368_, v_inst_369_, v_inst_370_, v___x_380_);
lean_inc(v_toBind_374_);
lean_inc_ref(v_inst_362_);
lean_inc(v_toPure_375_);
lean_inc_ref(v_inst_363_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__8___boxed), 16, 15);
lean_closure_set(v___f_382_, 0, v_inst_363_);
lean_closure_set(v___f_382_, 1, v_toPure_375_);
lean_closure_set(v___f_382_, 2, v___x_377_);
lean_closure_set(v___f_382_, 3, v_inst_365_);
lean_closure_set(v___f_382_, 4, v_inst_362_);
lean_closure_set(v___f_382_, 5, v_inst_368_);
lean_closure_set(v___f_382_, 6, v_inst_369_);
lean_closure_set(v___f_382_, 7, v_inst_370_);
lean_closure_set(v___f_382_, 8, v_toBind_374_);
lean_closure_set(v___f_382_, 9, v___x_378_);
lean_closure_set(v___f_382_, 10, v_attrInstance_372_);
lean_closure_set(v___f_382_, 11, v___f_376_);
lean_closure_set(v___f_382_, 12, v_inst_366_);
lean_closure_set(v___f_382_, 13, v_inst_367_);
lean_closure_set(v___f_382_, 14, v_inst_364_);
lean_inc(v_toBind_374_);
v___x_383_ = lean_apply_4(v_toBind_374_, lean_box(0), lean_box(0), v___x_381_, v___f_382_);
v___x_384_ = 1;
v___x_385_ = l_Lean_withoutExporting___redArg(v_inst_362_, v_inst_363_, v_inst_371_, v___x_383_, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr(lean_object* v_m_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_attrInstance_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_elabAttr___redArg(v_inst_387_, v_inst_388_, v_inst_389_, v_inst_390_, v_inst_391_, v_inst_392_, v_inst_393_, v_inst_394_, v_inst_395_, v_inst_397_, v_attrInstance_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___boxed(lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_attrInstance_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Elab_elabAttr(v_m_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_inst_406_, v_inst_407_, v_inst_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_attrInstance_412_);
lean_dec(v_inst_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0(lean_object* v_toPure_414_, lean_object* v_p_415_){
_start:
{
lean_object* v_snd_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_snd_416_ = lean_ctor_get(v_p_415_, 1);
lean_inc(v_snd_416_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_snd_416_);
v___x_418_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(lean_object* v_toPure_419_, lean_object* v_p_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_elabAttrs___redArg___lam__0(v_toPure_419_, v_p_420_);
lean_dec_ref(v_p_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1(lean_object* v_a_422_, lean_object* v_withRef_423_, lean_object* v___x_424_, lean_object* v_oldRef_425_){
_start:
{
lean_object* v_ref_426_; lean_object* v___x_427_; 
v_ref_426_ = l_Lean_replaceRef(v_a_422_, v_oldRef_425_);
v___x_427_ = lean_apply_3(v_withRef_423_, lean_box(0), v_ref_426_, v___x_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(lean_object* v_a_428_, lean_object* v_withRef_429_, lean_object* v___x_430_, lean_object* v_oldRef_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Elab_elabAttrs___redArg___lam__1(v_a_428_, v_withRef_429_, v___x_430_, v_oldRef_431_);
lean_dec(v_oldRef_431_);
lean_dec(v_a_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__2(lean_object* v___y_433_, lean_object* v_toPure_434_, lean_object* v_____do__lift_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = lean_array_push(v___y_433_, v_____do__lift_435_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
v___x_439_ = lean_apply_2(v_toPure_434_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__3(lean_object* v___y_440_, lean_object* v_toPure_441_, lean_object* v_____r_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_____r_442_);
lean_ctor_set(v___x_443_, 1, v___y_440_);
v___x_444_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__4(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_toBind_450_, lean_object* v___f_451_, lean_object* v_ex_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = l_Lean_Elab_logException___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_inst_448_, v_inst_449_, v_ex_452_);
v___x_454_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_453_, v___f_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5(lean_object* v_toMonadRef_455_, lean_object* v_toMonadExceptOf_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_toBind_467_, lean_object* v_toPure_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v___f_471_, lean_object* v_a_472_, lean_object* v_x_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_getRef_475_; lean_object* v_withRef_476_; lean_object* v_tryCatch_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_getRef_475_ = lean_ctor_get(v_toMonadRef_455_, 0);
lean_inc(v_getRef_475_);
v_withRef_476_ = lean_ctor_get(v_toMonadRef_455_, 1);
lean_inc(v_withRef_476_);
lean_dec_ref(v_toMonadRef_455_);
v_tryCatch_477_ = lean_ctor_get(v_toMonadExceptOf_456_, 1);
lean_inc(v_tryCatch_477_);
lean_dec_ref(v_toMonadExceptOf_456_);
lean_inc(v_a_472_);
lean_inc(v_inst_465_);
lean_inc(v_inst_464_);
lean_inc_ref(v_inst_457_);
v___x_478_ = l_Lean_Elab_elabAttr___redArg(v_inst_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_inst_461_, v_inst_462_, v_inst_463_, v_inst_464_, v_inst_465_, v_inst_466_, v_a_472_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_479_, 0, v_a_472_);
lean_closure_set(v___f_479_, 1, v_withRef_476_);
lean_closure_set(v___f_479_, 2, v___x_478_);
lean_inc(v_toBind_467_);
v___x_480_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v_getRef_475_, v___f_479_);
lean_inc(v_toPure_468_);
lean_inc_ref(v___y_474_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__2), 3, 2);
lean_closure_set(v___f_481_, 0, v___y_474_);
lean_closure_set(v___f_481_, 1, v_toPure_468_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__3), 3, 2);
lean_closure_set(v___f_482_, 0, v___y_474_);
lean_closure_set(v___f_482_, 1, v_toPure_468_);
lean_inc(v_toBind_467_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__4), 8, 7);
lean_closure_set(v___f_483_, 0, v_inst_457_);
lean_closure_set(v___f_483_, 1, v_inst_469_);
lean_closure_set(v___f_483_, 2, v_inst_465_);
lean_closure_set(v___f_483_, 3, v_inst_464_);
lean_closure_set(v___f_483_, 4, v_inst_470_);
lean_closure_set(v___f_483_, 5, v_toBind_467_);
lean_closure_set(v___f_483_, 6, v___f_482_);
lean_inc(v_toBind_467_);
v___x_484_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_480_, v___f_481_);
v___x_485_ = lean_apply_3(v_tryCatch_477_, lean_box(0), v___x_484_, v___f_483_);
v___x_486_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_485_, v___f_471_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toMonadRef_487_ = _args[0];
lean_object* v_toMonadExceptOf_488_ = _args[1];
lean_object* v_inst_489_ = _args[2];
lean_object* v_inst_490_ = _args[3];
lean_object* v_inst_491_ = _args[4];
lean_object* v_inst_492_ = _args[5];
lean_object* v_inst_493_ = _args[6];
lean_object* v_inst_494_ = _args[7];
lean_object* v_inst_495_ = _args[8];
lean_object* v_inst_496_ = _args[9];
lean_object* v_inst_497_ = _args[10];
lean_object* v_inst_498_ = _args[11];
lean_object* v_toBind_499_ = _args[12];
lean_object* v_toPure_500_ = _args[13];
lean_object* v_inst_501_ = _args[14];
lean_object* v_inst_502_ = _args[15];
lean_object* v___f_503_ = _args[16];
lean_object* v_a_504_ = _args[17];
lean_object* v_x_505_ = _args[18];
lean_object* v___y_506_ = _args[19];
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_elabAttrs___redArg___lam__5(v_toMonadRef_487_, v_toMonadExceptOf_488_, v_inst_489_, v_inst_490_, v_inst_491_, v_inst_492_, v_inst_493_, v_inst_494_, v_inst_495_, v_inst_496_, v_inst_497_, v_inst_498_, v_toBind_499_, v_toPure_500_, v_inst_501_, v_inst_502_, v___f_503_, v_a_504_, v_x_505_, v___y_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__6(lean_object* v_toPure_508_, lean_object* v_____s_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_apply_2(v_toPure_508_, lean_box(0), v_____s_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg(lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_attrInstances_525_){
_start:
{
lean_object* v_toApplicative_526_; lean_object* v_toBind_527_; lean_object* v_toMonadExceptOf_528_; lean_object* v_toMonadRef_529_; lean_object* v_toPure_530_; lean_object* v_attrs_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___f_534_; size_t v_sz_535_; size_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_toApplicative_526_ = lean_ctor_get(v_inst_513_, 0);
v_toBind_527_ = lean_ctor_get(v_inst_513_, 1);
lean_inc(v_toBind_527_);
v_toMonadExceptOf_528_ = lean_ctor_get(v_inst_516_, 0);
lean_inc_ref(v_toMonadExceptOf_528_);
v_toMonadRef_529_ = lean_ctor_get(v_inst_516_, 1);
lean_inc_ref(v_toMonadRef_529_);
v_toPure_530_ = lean_ctor_get(v_toApplicative_526_, 1);
v_attrs_531_ = ((lean_object*)(l_Lean_Elab_elabAttrs___redArg___closed__0));
lean_inc(v_toPure_530_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_532_, 0, v_toPure_530_);
lean_inc(v_toPure_530_);
lean_inc(v_toBind_527_);
lean_inc_ref(v_inst_513_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__5___boxed), 20, 17);
lean_closure_set(v___f_533_, 0, v_toMonadRef_529_);
lean_closure_set(v___f_533_, 1, v_toMonadExceptOf_528_);
lean_closure_set(v___f_533_, 2, v_inst_513_);
lean_closure_set(v___f_533_, 3, v_inst_514_);
lean_closure_set(v___f_533_, 4, v_inst_515_);
lean_closure_set(v___f_533_, 5, v_inst_516_);
lean_closure_set(v___f_533_, 6, v_inst_517_);
lean_closure_set(v___f_533_, 7, v_inst_518_);
lean_closure_set(v___f_533_, 8, v_inst_519_);
lean_closure_set(v___f_533_, 9, v_inst_520_);
lean_closure_set(v___f_533_, 10, v_inst_521_);
lean_closure_set(v___f_533_, 11, v_inst_524_);
lean_closure_set(v___f_533_, 12, v_toBind_527_);
lean_closure_set(v___f_533_, 13, v_toPure_530_);
lean_closure_set(v___f_533_, 14, v_inst_522_);
lean_closure_set(v___f_533_, 15, v_inst_523_);
lean_closure_set(v___f_533_, 16, v___f_532_);
lean_inc(v_toPure_530_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__6), 2, 1);
lean_closure_set(v___f_534_, 0, v_toPure_530_);
v_sz_535_ = lean_array_size(v_attrInstances_525_);
v___x_536_ = ((size_t)0ULL);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_513_, v_attrInstances_525_, v___f_533_, v_sz_535_, v___x_536_, v_attrs_531_);
v___x_538_ = lean_apply_4(v_toBind_527_, lean_box(0), lean_box(0), v___x_537_, v___f_534_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs(lean_object* v_m_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_attrInstances_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Elab_elabAttrs___redArg(v_inst_540_, v_inst_541_, v_inst_542_, v_inst_543_, v_inst_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_inst_548_, v_inst_549_, v_inst_550_, v_inst_551_, v_attrInstances_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_stx_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = l_Lean_Syntax_getArg(v_stx_566_, v___x_567_);
v___x_569_ = l_Lean_Syntax_getSepArgs(v___x_568_);
lean_dec(v___x_568_);
v___x_570_ = l_Lean_Elab_elabAttrs___redArg(v_inst_554_, v_inst_555_, v_inst_556_, v_inst_557_, v_inst_558_, v_inst_559_, v_inst_560_, v_inst_561_, v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___boxed(lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_stx_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_stx_583_);
lean_dec(v_stx_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* v_m_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_stx_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_, v_inst_597_, v_stx_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___boxed(lean_object* v_m_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_stx_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_elabDeclAttrs(v_m_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_inst_608_, v_inst_609_, v_inst_610_, v_inst_611_, v_inst_612_, v_stx_613_);
lean_dec(v_stx_613_);
return v_res_614_;
}
}
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif
