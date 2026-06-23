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
extern lean_object* l_Lean_regularInitAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot use attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "]`: module `"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__3;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "` is loaded for IR only (reached as a private `meta` dependency). Add an import of `"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__4 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__5___closed__4_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__5;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__6 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__5___closed__6_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__8___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]`"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__8___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__0_value;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___closed__1 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__1_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_toAttributeKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__1_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unknown attribute"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___closed__3 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__13___closed__3_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v___y_25_);
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
v___x_88_ = ((lean_object*)(l_Lean_Elab_toAttributeKind___closed__5));
lean_inc(v_ref_87_);
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
lean_dec_ref(v_a_107_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_ref_171_, uint8_t v___x_172_, lean_object* v_toBind_173_, lean_object* v___f_174_, lean_object* v_____r_175_){
_start:
{
lean_object* v_toMonadRef_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_toMonadRef_176_ = lean_ctor_get(v_inst_165_, 1);
lean_inc_ref(v_toMonadRef_176_);
lean_dec_ref(v_inst_165_);
v___x_177_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_166_, v_inst_167_, v_inst_168_, v_inst_169_, v_toMonadRef_176_, v_inst_170_, v_ref_171_, v___x_172_);
v___x_178_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v___x_177_, v___f_174_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3___boxed(lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_ref_185_, lean_object* v___x_186_, lean_object* v_toBind_187_, lean_object* v___f_188_, lean_object* v_____r_189_){
_start:
{
uint8_t v___x_1457__boxed_190_; lean_object* v_res_191_; 
v___x_1457__boxed_190_ = lean_unbox(v___x_186_);
v_res_191_ = l_Lean_Elab_elabAttr___redArg___lam__3(v_inst_179_, v_inst_180_, v_inst_181_, v_inst_182_, v_inst_183_, v_inst_184_, v_ref_185_, v___x_1457__boxed_190_, v_toBind_187_, v___f_188_, v_____r_189_);
return v_res_191_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__0));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__2));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__4));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__6));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object* v___f_204_, lean_object* v_val_205_, lean_object* v_attrName_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_toBind_209_, lean_object* v___f_210_, lean_object* v_env_211_){
_start:
{
lean_object* v___x_215_; lean_object* v_modules_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_215_ = l_Lean_Environment_header(v_env_211_);
v_modules_216_ = lean_ctor_get(v___x_215_, 3);
lean_inc_ref(v_modules_216_);
lean_dec_ref(v___x_215_);
v___x_217_ = lean_array_get_size(v_modules_216_);
v___x_218_ = lean_nat_dec_lt(v_val_205_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v_modules_216_);
lean_dec(v___f_210_);
lean_dec(v_toBind_209_);
lean_dec_ref(v_inst_208_);
lean_dec_ref(v_inst_207_);
lean_dec(v_attrName_206_);
goto v___jp_212_;
}
else
{
lean_object* v___x_219_; uint8_t v_hasData_220_; 
v___x_219_ = lean_array_fget_borrowed(v_modules_216_, v_val_205_);
v_hasData_220_ = lean_ctor_get_uint8(v___x_219_, sizeof(void*)*1 + 1);
if (v_hasData_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_toImport_223_; lean_object* v_module_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v___f_204_);
v___x_221_ = l_Lean_instInhabitedEffectiveImport_default;
v___x_222_ = lean_array_get(v___x_221_, v_modules_216_, v_val_205_);
lean_dec_ref(v_modules_216_);
v_toImport_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_toImport_223_);
lean_dec(v___x_222_);
v_module_224_ = lean_ctor_get(v_toImport_223_, 0);
lean_inc(v_module_224_);
lean_dec_ref(v_toImport_223_);
v___x_225_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1);
v___x_226_ = l_Lean_MessageData_ofName(v_attrName_206_);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l_Lean_MessageData_ofName(v_module_224_);
lean_inc_ref(v___x_230_);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__5, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_230_);
v___x_235_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__7, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Lean_throwError___redArg(v_inst_207_, v_inst_208_, v___x_236_);
v___x_238_ = lean_apply_4(v_toBind_209_, lean_box(0), lean_box(0), v___x_237_, v___f_210_);
return v___x_238_;
}
else
{
lean_dec_ref(v_modules_216_);
lean_dec(v___f_210_);
lean_dec(v_toBind_209_);
lean_dec_ref(v_inst_208_);
lean_dec_ref(v_inst_207_);
lean_dec(v_attrName_206_);
goto v___jp_212_;
}
}
v___jp_212_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v___f_204_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___boxed(lean_object* v___f_239_, lean_object* v_val_240_, lean_object* v_attrName_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_toBind_244_, lean_object* v___f_245_, lean_object* v_env_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_elabAttr___redArg___lam__5(v___f_239_, v_val_240_, v_attrName_241_, v_inst_242_, v_inst_243_, v_toBind_244_, v___f_245_, v_env_246_);
lean_dec_ref(v_env_246_);
lean_dec(v_val_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object* v_ref_248_, lean_object* v___f_249_, lean_object* v_attrName_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_toBind_253_, lean_object* v___f_254_, lean_object* v_getEnv_255_, lean_object* v_____do__lift_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_256_, v_ref_248_);
if (lean_obj_tag(v___x_257_) == 1)
{
lean_object* v_val_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v_val_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_val_258_);
lean_dec_ref_known(v___x_257_, 1);
lean_inc(v_toBind_253_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_259_, 0, v___f_249_);
lean_closure_set(v___f_259_, 1, v_val_258_);
lean_closure_set(v___f_259_, 2, v_attrName_250_);
lean_closure_set(v___f_259_, 3, v_inst_251_);
lean_closure_set(v___f_259_, 4, v_inst_252_);
lean_closure_set(v___f_259_, 5, v_toBind_253_);
lean_closure_set(v___f_259_, 6, v___f_254_);
v___x_260_ = lean_apply_4(v_toBind_253_, lean_box(0), lean_box(0), v_getEnv_255_, v___f_259_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v___x_257_);
lean_dec(v_getEnv_255_);
lean_dec(v___f_254_);
lean_dec(v_toBind_253_);
lean_dec_ref(v_inst_252_);
lean_dec_ref(v_inst_251_);
lean_dec(v_attrName_250_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_apply_1(v___f_249_, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4___boxed(lean_object* v_ref_263_, lean_object* v___f_264_, lean_object* v_attrName_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_toBind_268_, lean_object* v___f_269_, lean_object* v_getEnv_270_, lean_object* v_____do__lift_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_elabAttr___redArg___lam__4(v_ref_263_, v___f_264_, v_attrName_265_, v_inst_266_, v_inst_267_, v_toBind_268_, v___f_269_, v_getEnv_270_, v_____do__lift_271_);
lean_dec_ref(v_____do__lift_271_);
lean_dec(v_ref_263_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object* v_a_273_, lean_object* v___x_274_, lean_object* v___f_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_toBind_282_, lean_object* v___f_283_, lean_object* v_attrName_284_, lean_object* v_getEnv_285_, lean_object* v_____do__lift_286_){
_start:
{
lean_object* v_toAttributeImplCore_287_; lean_object* v_ref_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_toAttributeImplCore_287_ = lean_ctor_get(v_a_273_, 0);
lean_inc_ref(v_toAttributeImplCore_287_);
lean_dec_ref(v_a_273_);
v_ref_288_ = lean_ctor_get(v_toAttributeImplCore_287_, 0);
lean_inc_n(v_ref_288_, 2);
lean_dec_ref(v_toAttributeImplCore_287_);
v___x_289_ = l_Lean_regularInitAttr;
v___x_290_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_274_, v___x_289_, v_____do__lift_286_, v_ref_288_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_ref_288_);
lean_dec(v_getEnv_285_);
lean_dec(v_attrName_284_);
lean_dec(v___f_283_);
lean_dec(v_toBind_282_);
lean_dec(v_inst_281_);
lean_dec(v_inst_280_);
lean_dec_ref(v_inst_279_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
lean_dec_ref(v_inst_276_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_apply_1(v___f_275_, v___x_291_);
return v___x_292_;
}
else
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___x_298_; 
lean_dec_ref_known(v___x_290_, 1);
lean_dec(v___f_275_);
v___x_293_ = 1;
v___x_294_ = lean_box(v___x_293_);
lean_inc_n(v_toBind_282_, 2);
lean_inc(v_ref_288_);
lean_inc_ref(v_inst_277_);
lean_inc_ref(v_inst_276_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_295_, 0, v_inst_276_);
lean_closure_set(v___f_295_, 1, v_inst_277_);
lean_closure_set(v___f_295_, 2, v_inst_278_);
lean_closure_set(v___f_295_, 3, v_inst_279_);
lean_closure_set(v___f_295_, 4, v_inst_280_);
lean_closure_set(v___f_295_, 5, v_inst_281_);
lean_closure_set(v___f_295_, 6, v_ref_288_);
lean_closure_set(v___f_295_, 7, v___x_294_);
lean_closure_set(v___f_295_, 8, v_toBind_282_);
lean_closure_set(v___f_295_, 9, v___f_283_);
lean_inc_ref(v___f_295_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_296_, 0, v___f_295_);
lean_inc(v_getEnv_285_);
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_297_, 0, v_ref_288_);
lean_closure_set(v___f_297_, 1, v___f_295_);
lean_closure_set(v___f_297_, 2, v_attrName_284_);
lean_closure_set(v___f_297_, 3, v_inst_277_);
lean_closure_set(v___f_297_, 4, v_inst_276_);
lean_closure_set(v___f_297_, 5, v_toBind_282_);
lean_closure_set(v___f_297_, 6, v___f_296_);
lean_closure_set(v___f_297_, 7, v_getEnv_285_);
v___x_298_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v_getEnv_285_, v___f_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object* v_attrName_299_, lean_object* v___x_300_, lean_object* v___f_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_toBind_308_, lean_object* v___f_309_, lean_object* v_getEnv_310_, lean_object* v_____do__lift_311_){
_start:
{
lean_object* v___x_312_; 
lean_inc(v_attrName_299_);
v___x_312_ = l_Lean_getAttributeImpl(v_____do__lift_311_, v_attrName_299_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_a_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
lean_inc(v_getEnv_310_);
lean_inc(v_toBind_308_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__6), 14, 13);
lean_closure_set(v___f_314_, 0, v_a_313_);
lean_closure_set(v___f_314_, 1, v___x_300_);
lean_closure_set(v___f_314_, 2, v___f_301_);
lean_closure_set(v___f_314_, 3, v_inst_302_);
lean_closure_set(v___f_314_, 4, v_inst_303_);
lean_closure_set(v___f_314_, 5, v_inst_304_);
lean_closure_set(v___f_314_, 6, v_inst_305_);
lean_closure_set(v___f_314_, 7, v_inst_306_);
lean_closure_set(v___f_314_, 8, v_inst_307_);
lean_closure_set(v___f_314_, 9, v_toBind_308_);
lean_closure_set(v___f_314_, 10, v___f_309_);
lean_closure_set(v___f_314_, 11, v_attrName_299_);
lean_closure_set(v___f_314_, 12, v_getEnv_310_);
v___x_315_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v_getEnv_310_, v___f_314_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec_ref(v___x_312_);
lean_dec(v_getEnv_310_);
lean_dec(v___f_309_);
lean_dec(v_toBind_308_);
lean_dec(v_inst_307_);
lean_dec(v_inst_306_);
lean_dec_ref(v_inst_305_);
lean_dec_ref(v_inst_304_);
lean_dec_ref(v_inst_303_);
lean_dec_ref(v_inst_302_);
lean_dec(v___x_300_);
lean_dec(v_attrName_299_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v___f_301_, v___x_316_);
return v___x_317_;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__0));
v___x_320_ = l_Lean_stringToMessageData(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__2));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object* v_attrName_324_, lean_object* v_toBind_325_, lean_object* v_getEnv_326_, lean_object* v___f_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_____do__lift_330_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v_attrName_324_);
v___x_331_ = l_Lean_getAttributeImpl(v_____do__lift_330_, v_attrName_324_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v___x_332_; 
lean_dec_ref_known(v___x_331_, 1);
lean_dec_ref(v_inst_329_);
lean_dec_ref(v_inst_328_);
lean_dec(v_attrName_324_);
v___x_332_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v_getEnv_326_, v___f_327_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v___x_331_);
lean_dec(v___f_327_);
lean_dec(v_getEnv_326_);
lean_dec(v_toBind_325_);
v___x_333_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1);
v___x_334_ = l_Lean_MessageData_ofName(v_attrName_324_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_throwError___redArg(v_inst_328_, v_inst_329_, v___x_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9(lean_object* v_inst_339_, uint8_t v_attrKind_340_, lean_object* v_attr_341_, lean_object* v_toPure_342_, lean_object* v___x_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_toBind_349_, lean_object* v_attrName_350_){
_start:
{
lean_object* v_getEnv_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v___f_356_; lean_object* v___x_357_; 
v_getEnv_351_ = lean_ctor_get(v_inst_339_, 0);
lean_inc_n(v_getEnv_351_, 3);
v___x_352_ = lean_box(v_attrKind_340_);
lean_inc_n(v_attrName_350_, 2);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_353_, 0, v___x_352_);
lean_closure_set(v___f_353_, 1, v_attrName_350_);
lean_closure_set(v___f_353_, 2, v_attr_341_);
lean_closure_set(v___f_353_, 3, v_toPure_342_);
lean_inc_ref(v___f_353_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_354_, 0, v___f_353_);
lean_inc_n(v_toBind_349_, 2);
lean_inc_ref(v_inst_345_);
lean_inc_ref(v_inst_344_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 13, 12);
lean_closure_set(v___f_355_, 0, v_attrName_350_);
lean_closure_set(v___f_355_, 1, v___x_343_);
lean_closure_set(v___f_355_, 2, v___f_353_);
lean_closure_set(v___f_355_, 3, v_inst_344_);
lean_closure_set(v___f_355_, 4, v_inst_345_);
lean_closure_set(v___f_355_, 5, v_inst_339_);
lean_closure_set(v___f_355_, 6, v_inst_346_);
lean_closure_set(v___f_355_, 7, v_inst_347_);
lean_closure_set(v___f_355_, 8, v_inst_348_);
lean_closure_set(v___f_355_, 9, v_toBind_349_);
lean_closure_set(v___f_355_, 10, v___f_354_);
lean_closure_set(v___f_355_, 11, v_getEnv_351_);
v___f_356_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__8), 7, 6);
lean_closure_set(v___f_356_, 0, v_attrName_350_);
lean_closure_set(v___f_356_, 1, v_toBind_349_);
lean_closure_set(v___f_356_, 2, v_getEnv_351_);
lean_closure_set(v___f_356_, 3, v___f_355_);
lean_closure_set(v___f_356_, 4, v_inst_345_);
lean_closure_set(v___f_356_, 5, v_inst_344_);
v___x_357_ = lean_apply_4(v_toBind_349_, lean_box(0), lean_box(0), v_getEnv_351_, v___f_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9___boxed(lean_object* v_inst_358_, lean_object* v_attrKind_359_, lean_object* v_attr_360_, lean_object* v_toPure_361_, lean_object* v___x_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_toBind_368_, lean_object* v_attrName_369_){
_start:
{
uint8_t v_attrKind_boxed_370_; lean_object* v_res_371_; 
v_attrKind_boxed_370_ = lean_unbox(v_attrKind_359_);
v_res_371_ = l_Lean_Elab_elabAttr___redArg___lam__9(v_inst_358_, v_attrKind_boxed_370_, v_attr_360_, v_toPure_361_, v___x_362_, v_inst_363_, v_inst_364_, v_inst_365_, v_inst_366_, v_inst_367_, v_toBind_368_, v_attrName_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object* v___f_372_, lean_object* v_attrName_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_apply_1(v___f_372_, v_attrName_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__3));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13(lean_object* v_inst_385_, uint8_t v_attrKind_386_, lean_object* v_toPure_387_, lean_object* v___x_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_toBind_394_, lean_object* v___x_395_, lean_object* v_attr_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_397_ = lean_box(v_attrKind_386_);
lean_inc(v_toBind_394_);
lean_inc_ref(v_inst_390_);
lean_inc_ref(v_inst_389_);
lean_inc(v_toPure_387_);
lean_inc_n(v_attr_396_, 2);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__9___boxed), 12, 11);
lean_closure_set(v___f_398_, 0, v_inst_385_);
lean_closure_set(v___f_398_, 1, v___x_397_);
lean_closure_set(v___f_398_, 2, v_attr_396_);
lean_closure_set(v___f_398_, 3, v_toPure_387_);
lean_closure_set(v___f_398_, 4, v___x_388_);
lean_closure_set(v___f_398_, 5, v_inst_389_);
lean_closure_set(v___f_398_, 6, v_inst_390_);
lean_closure_set(v___f_398_, 7, v_inst_391_);
lean_closure_set(v___f_398_, 8, v_inst_392_);
lean_closure_set(v___f_398_, 9, v_inst_393_);
lean_closure_set(v___f_398_, 10, v_toBind_394_);
v___x_399_ = l_Lean_Syntax_getKind(v_attr_396_);
v___x_400_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2));
v___x_401_ = lean_name_eq(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
if (lean_obj_tag(v___x_399_) == 1)
{
lean_object* v_str_402_; lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_attr_396_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
v_str_402_ = lean_ctor_get(v___x_399_, 1);
lean_inc_ref(v_str_402_);
lean_dec_ref_known(v___x_399_, 2);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_403_, 0, v___f_398_);
v___x_404_ = lean_box(0);
v___x_405_ = l_Lean_Name_str___override(v___x_404_, v_str_402_);
v___x_406_ = lean_apply_2(v_toPure_387_, lean_box(0), v___x_405_);
v___x_407_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v___x_406_, v___f_403_);
return v___x_407_;
}
else
{
lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v___x_399_);
lean_dec(v_toPure_387_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_408_, 0, v___f_398_);
v___x_409_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__13___closed__4, &l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once, _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4);
v___x_410_ = l_Lean_throwErrorAt___redArg(v_inst_390_, v_inst_389_, v_attr_396_, v___x_409_);
v___x_411_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v___x_410_, v___f_408_);
return v___x_411_;
}
}
else
{
lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v___x_399_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_412_, 0, v___f_398_);
v___x_413_ = l_Lean_Syntax_getArg(v_attr_396_, v___x_395_);
lean_dec(v_attr_396_);
v___x_414_ = l_Lean_Syntax_getId(v___x_413_);
lean_dec(v___x_413_);
v___x_415_ = lean_erase_macro_scopes(v___x_414_);
v___x_416_ = lean_apply_2(v_toPure_387_, lean_box(0), v___x_415_);
v___x_417_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v___x_416_, v___f_412_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___boxed(lean_object* v_inst_418_, lean_object* v_attrKind_419_, lean_object* v_toPure_420_, lean_object* v___x_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_toBind_427_, lean_object* v___x_428_, lean_object* v_attr_429_){
_start:
{
uint8_t v_attrKind_boxed_430_; lean_object* v_res_431_; 
v_attrKind_boxed_430_ = lean_unbox(v_attrKind_419_);
v_res_431_ = l_Lean_Elab_elabAttr___redArg___lam__13(v_inst_418_, v_attrKind_boxed_430_, v_toPure_420_, v___x_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_inst_425_, v_inst_426_, v_toBind_427_, v___x_428_, v_attr_429_);
lean_dec(v___x_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11(lean_object* v_inst_432_, lean_object* v_toPure_433_, lean_object* v___x_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_toBind_440_, lean_object* v___x_441_, lean_object* v_attrInstance_442_, lean_object* v___f_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, uint8_t v_attrKind_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___f_449_; lean_object* v___x_450_; lean_object* v_attr_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_448_ = lean_box(v_attrKind_447_);
lean_inc(v_toBind_440_);
lean_inc(v_inst_439_);
lean_inc(v_inst_438_);
lean_inc_ref(v_inst_437_);
lean_inc_ref(v_inst_436_);
lean_inc_ref(v_inst_435_);
lean_inc_ref(v_inst_432_);
v___f_449_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_449_, 0, v_inst_432_);
lean_closure_set(v___f_449_, 1, v___x_448_);
lean_closure_set(v___f_449_, 2, v_toPure_433_);
lean_closure_set(v___f_449_, 3, v___x_434_);
lean_closure_set(v___f_449_, 4, v_inst_435_);
lean_closure_set(v___f_449_, 5, v_inst_436_);
lean_closure_set(v___f_449_, 6, v_inst_437_);
lean_closure_set(v___f_449_, 7, v_inst_438_);
lean_closure_set(v___f_449_, 8, v_inst_439_);
lean_closure_set(v___f_449_, 9, v_toBind_440_);
lean_closure_set(v___f_449_, 10, v___x_441_);
v___x_450_ = lean_unsigned_to_nat(1u);
v_attr_451_ = l_Lean_Syntax_getArg(v_attrInstance_442_, v___x_450_);
v___x_452_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_452_, 0, v_attr_451_);
lean_closure_set(v___x_452_, 1, v___f_443_);
v___x_453_ = l_Lean_Elab_liftMacroM___redArg(v_inst_436_, v_inst_444_, v_inst_432_, v_inst_445_, v_inst_435_, v_inst_446_, v_inst_437_, v_inst_438_, v_inst_439_, v___x_452_);
v___x_454_ = lean_apply_4(v_toBind_440_, lean_box(0), lean_box(0), v___x_453_, v___f_449_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11___boxed(lean_object* v_inst_455_, lean_object* v_toPure_456_, lean_object* v___x_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_toBind_463_, lean_object* v___x_464_, lean_object* v_attrInstance_465_, lean_object* v___f_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_attrKind_470_){
_start:
{
uint8_t v_attrKind_boxed_471_; lean_object* v_res_472_; 
v_attrKind_boxed_471_ = lean_unbox(v_attrKind_470_);
v_res_472_ = l_Lean_Elab_elabAttr___redArg___lam__11(v_inst_455_, v_toPure_456_, v___x_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_inst_461_, v_inst_462_, v_toBind_463_, v___x_464_, v_attrInstance_465_, v___f_466_, v_inst_467_, v_inst_468_, v_inst_469_, v_attrKind_boxed_471_);
lean_dec(v_attrInstance_465_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg(lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_attrInstance_484_){
_start:
{
lean_object* v_toApplicative_485_; lean_object* v_toBind_486_; lean_object* v_toPure_487_; lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___f_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_474_, 0);
v_toBind_486_ = lean_ctor_get(v_inst_474_, 1);
v_toPure_487_ = lean_ctor_get(v_toApplicative_485_, 1);
v___f_488_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___closed__0));
v___x_489_ = lean_box(0);
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Lean_Syntax_getArg(v_attrInstance_484_, v___x_490_);
v___x_492_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_492_, 0, v___x_491_);
lean_inc(v_inst_482_);
lean_inc(v_inst_481_);
lean_inc_ref(v_inst_480_);
lean_inc_ref(v_inst_476_);
lean_inc_ref(v_inst_477_);
lean_inc_ref(v_inst_479_);
lean_inc_ref_n(v_inst_475_, 2);
lean_inc_ref(v_inst_478_);
lean_inc_ref_n(v_inst_474_, 2);
v___x_493_ = l_Lean_Elab_liftMacroM___redArg(v_inst_474_, v_inst_478_, v_inst_475_, v_inst_479_, v_inst_477_, v_inst_476_, v_inst_480_, v_inst_481_, v_inst_482_, v___x_492_);
lean_inc_n(v_toBind_486_, 2);
lean_inc(v_toPure_487_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_494_, 0, v_inst_475_);
lean_closure_set(v___f_494_, 1, v_toPure_487_);
lean_closure_set(v___f_494_, 2, v___x_489_);
lean_closure_set(v___f_494_, 3, v_inst_477_);
lean_closure_set(v___f_494_, 4, v_inst_474_);
lean_closure_set(v___f_494_, 5, v_inst_480_);
lean_closure_set(v___f_494_, 6, v_inst_481_);
lean_closure_set(v___f_494_, 7, v_inst_482_);
lean_closure_set(v___f_494_, 8, v_toBind_486_);
lean_closure_set(v___f_494_, 9, v___x_490_);
lean_closure_set(v___f_494_, 10, v_attrInstance_484_);
lean_closure_set(v___f_494_, 11, v___f_488_);
lean_closure_set(v___f_494_, 12, v_inst_478_);
lean_closure_set(v___f_494_, 13, v_inst_479_);
lean_closure_set(v___f_494_, 14, v_inst_476_);
v___x_495_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_493_, v___f_494_);
v___x_496_ = 1;
v___x_497_ = l_Lean_withoutExporting___redArg(v_inst_474_, v_inst_475_, v_inst_483_, v___x_495_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr(lean_object* v_m_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_attrInstance_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Elab_elabAttr___redArg(v_inst_499_, v_inst_500_, v_inst_501_, v_inst_502_, v_inst_503_, v_inst_504_, v_inst_505_, v_inst_506_, v_inst_507_, v_inst_509_, v_attrInstance_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___boxed(lean_object* v_m_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_attrInstance_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Elab_elabAttr(v_m_512_, v_inst_513_, v_inst_514_, v_inst_515_, v_inst_516_, v_inst_517_, v_inst_518_, v_inst_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_inst_523_, v_attrInstance_524_);
lean_dec(v_inst_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0(lean_object* v_toPure_526_, lean_object* v_p_527_){
_start:
{
lean_object* v_snd_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_snd_528_ = lean_ctor_get(v_p_527_, 1);
lean_inc(v_snd_528_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_snd_528_);
v___x_530_ = lean_apply_2(v_toPure_526_, lean_box(0), v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(lean_object* v_toPure_531_, lean_object* v_p_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Elab_elabAttrs___redArg___lam__0(v_toPure_531_, v_p_532_);
lean_dec_ref(v_p_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1(lean_object* v_a_534_, lean_object* v_withRef_535_, lean_object* v___x_536_, lean_object* v_oldRef_537_){
_start:
{
lean_object* v_ref_538_; lean_object* v___x_539_; 
v_ref_538_ = l_Lean_replaceRef(v_a_534_, v_oldRef_537_);
v___x_539_ = lean_apply_3(v_withRef_535_, lean_box(0), v_ref_538_, v___x_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(lean_object* v_a_540_, lean_object* v_withRef_541_, lean_object* v___x_542_, lean_object* v_oldRef_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_elabAttrs___redArg___lam__1(v_a_540_, v_withRef_541_, v___x_542_, v_oldRef_543_);
lean_dec(v_oldRef_543_);
lean_dec(v_a_540_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__2(lean_object* v___y_545_, lean_object* v_toPure_546_, lean_object* v_____do__lift_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = lean_array_push(v___y_545_, v_____do__lift_547_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
v___x_551_ = lean_apply_2(v_toPure_546_, lean_box(0), v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__3(lean_object* v___y_552_, lean_object* v_toPure_553_, lean_object* v_____r_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_____r_554_);
lean_ctor_set(v___x_555_, 1, v___y_552_);
v___x_556_ = lean_apply_2(v_toPure_553_, lean_box(0), v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__4(lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_toBind_562_, lean_object* v___f_563_, lean_object* v_ex_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = l_Lean_Elab_logException___redArg(v_inst_557_, v_inst_558_, v_inst_559_, v_inst_560_, v_inst_561_, v_ex_564_);
v___x_566_ = lean_apply_4(v_toBind_562_, lean_box(0), lean_box(0), v___x_565_, v___f_563_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5(lean_object* v_toMonadRef_567_, lean_object* v_toMonadExceptOf_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_toBind_579_, lean_object* v_toPure_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v___f_583_, lean_object* v_a_584_, lean_object* v_x_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_getRef_587_; lean_object* v_withRef_588_; lean_object* v_tryCatch_589_; lean_object* v___x_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_getRef_587_ = lean_ctor_get(v_toMonadRef_567_, 0);
lean_inc(v_getRef_587_);
v_withRef_588_ = lean_ctor_get(v_toMonadRef_567_, 1);
lean_inc(v_withRef_588_);
lean_dec_ref(v_toMonadRef_567_);
v_tryCatch_589_ = lean_ctor_get(v_toMonadExceptOf_568_, 1);
lean_inc(v_tryCatch_589_);
lean_dec_ref(v_toMonadExceptOf_568_);
lean_inc(v_a_584_);
lean_inc(v_inst_577_);
lean_inc(v_inst_576_);
lean_inc_ref(v_inst_569_);
v___x_590_ = l_Lean_Elab_elabAttr___redArg(v_inst_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_a_584_);
v___f_591_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_591_, 0, v_a_584_);
lean_closure_set(v___f_591_, 1, v_withRef_588_);
lean_closure_set(v___f_591_, 2, v___x_590_);
lean_inc_n(v_toBind_579_, 3);
v___x_592_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v_getRef_587_, v___f_591_);
lean_inc(v_toPure_580_);
lean_inc_ref(v___y_586_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__2), 3, 2);
lean_closure_set(v___f_593_, 0, v___y_586_);
lean_closure_set(v___f_593_, 1, v_toPure_580_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__3), 3, 2);
lean_closure_set(v___f_594_, 0, v___y_586_);
lean_closure_set(v___f_594_, 1, v_toPure_580_);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__4), 8, 7);
lean_closure_set(v___f_595_, 0, v_inst_569_);
lean_closure_set(v___f_595_, 1, v_inst_581_);
lean_closure_set(v___f_595_, 2, v_inst_577_);
lean_closure_set(v___f_595_, 3, v_inst_576_);
lean_closure_set(v___f_595_, 4, v_inst_582_);
lean_closure_set(v___f_595_, 5, v_toBind_579_);
lean_closure_set(v___f_595_, 6, v___f_594_);
v___x_596_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_592_, v___f_593_);
v___x_597_ = lean_apply_3(v_tryCatch_589_, lean_box(0), v___x_596_, v___f_595_);
v___x_598_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_597_, v___f_583_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toMonadRef_599_ = _args[0];
lean_object* v_toMonadExceptOf_600_ = _args[1];
lean_object* v_inst_601_ = _args[2];
lean_object* v_inst_602_ = _args[3];
lean_object* v_inst_603_ = _args[4];
lean_object* v_inst_604_ = _args[5];
lean_object* v_inst_605_ = _args[6];
lean_object* v_inst_606_ = _args[7];
lean_object* v_inst_607_ = _args[8];
lean_object* v_inst_608_ = _args[9];
lean_object* v_inst_609_ = _args[10];
lean_object* v_inst_610_ = _args[11];
lean_object* v_toBind_611_ = _args[12];
lean_object* v_toPure_612_ = _args[13];
lean_object* v_inst_613_ = _args[14];
lean_object* v_inst_614_ = _args[15];
lean_object* v___f_615_ = _args[16];
lean_object* v_a_616_ = _args[17];
lean_object* v_x_617_ = _args[18];
lean_object* v___y_618_ = _args[19];
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Elab_elabAttrs___redArg___lam__5(v_toMonadRef_599_, v_toMonadExceptOf_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_inst_608_, v_inst_609_, v_inst_610_, v_toBind_611_, v_toPure_612_, v_inst_613_, v_inst_614_, v___f_615_, v_a_616_, v_x_617_, v___y_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__6(lean_object* v_toPure_620_, lean_object* v_____s_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_apply_2(v_toPure_620_, lean_box(0), v_____s_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg(lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_attrInstances_637_){
_start:
{
lean_object* v_toApplicative_638_; lean_object* v_toBind_639_; lean_object* v_toMonadExceptOf_640_; lean_object* v_toMonadRef_641_; lean_object* v_toPure_642_; lean_object* v_attrs_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___f_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_toApplicative_638_ = lean_ctor_get(v_inst_625_, 0);
v_toBind_639_ = lean_ctor_get(v_inst_625_, 1);
lean_inc_n(v_toBind_639_, 2);
v_toMonadExceptOf_640_ = lean_ctor_get(v_inst_628_, 0);
lean_inc_ref(v_toMonadExceptOf_640_);
v_toMonadRef_641_ = lean_ctor_get(v_inst_628_, 1);
lean_inc_ref(v_toMonadRef_641_);
v_toPure_642_ = lean_ctor_get(v_toApplicative_638_, 1);
v_attrs_643_ = ((lean_object*)(l_Lean_Elab_elabAttrs___redArg___closed__0));
lean_inc_n(v_toPure_642_, 3);
v___f_644_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_644_, 0, v_toPure_642_);
lean_inc_ref(v_inst_625_);
v___f_645_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__5___boxed), 20, 17);
lean_closure_set(v___f_645_, 0, v_toMonadRef_641_);
lean_closure_set(v___f_645_, 1, v_toMonadExceptOf_640_);
lean_closure_set(v___f_645_, 2, v_inst_625_);
lean_closure_set(v___f_645_, 3, v_inst_626_);
lean_closure_set(v___f_645_, 4, v_inst_627_);
lean_closure_set(v___f_645_, 5, v_inst_628_);
lean_closure_set(v___f_645_, 6, v_inst_629_);
lean_closure_set(v___f_645_, 7, v_inst_630_);
lean_closure_set(v___f_645_, 8, v_inst_631_);
lean_closure_set(v___f_645_, 9, v_inst_632_);
lean_closure_set(v___f_645_, 10, v_inst_633_);
lean_closure_set(v___f_645_, 11, v_inst_636_);
lean_closure_set(v___f_645_, 12, v_toBind_639_);
lean_closure_set(v___f_645_, 13, v_toPure_642_);
lean_closure_set(v___f_645_, 14, v_inst_634_);
lean_closure_set(v___f_645_, 15, v_inst_635_);
lean_closure_set(v___f_645_, 16, v___f_644_);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__6), 2, 1);
lean_closure_set(v___f_646_, 0, v_toPure_642_);
v_sz_647_ = lean_array_size(v_attrInstances_637_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_625_, v_attrInstances_637_, v___f_645_, v_sz_647_, v___x_648_, v_attrs_643_);
v___x_650_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v___x_649_, v___f_646_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs(lean_object* v_m_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_attrInstances_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Elab_elabAttrs___redArg(v_inst_652_, v_inst_653_, v_inst_654_, v_inst_655_, v_inst_656_, v_inst_657_, v_inst_658_, v_inst_659_, v_inst_660_, v_inst_661_, v_inst_662_, v_inst_663_, v_attrInstances_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_stx_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = l_Lean_Syntax_getArg(v_stx_678_, v___x_679_);
v___x_681_ = l_Lean_Syntax_getSepArgs(v___x_680_);
lean_dec(v___x_680_);
v___x_682_ = l_Lean_Elab_elabAttrs___redArg(v_inst_666_, v_inst_667_, v_inst_668_, v_inst_669_, v_inst_670_, v_inst_671_, v_inst_672_, v_inst_673_, v_inst_674_, v_inst_675_, v_inst_676_, v_inst_677_, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___boxed(lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_stx_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_683_, v_inst_684_, v_inst_685_, v_inst_686_, v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_inst_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_stx_695_);
lean_dec(v_stx_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* v_m_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_stx_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_698_, v_inst_699_, v_inst_700_, v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_inst_706_, v_inst_707_, v_inst_708_, v_inst_709_, v_stx_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___boxed(lean_object* v_m_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_stx_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Elab_elabDeclAttrs(v_m_712_, v_inst_713_, v_inst_714_, v_inst_715_, v_inst_716_, v_inst_717_, v_inst_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_inst_722_, v_inst_723_, v_inst_724_, v_stx_725_);
lean_dec(v_stx_725_);
return v_res_726_;
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
