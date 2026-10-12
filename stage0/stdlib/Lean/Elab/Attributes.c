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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
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
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__8___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___redArg___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]`"};
static const lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___redArg___lam__8___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___redArg___lam__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11___boxed(lean_object**);
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
uint8_t l_Lean_Elab_elabAttr___redArg___lam__0(lean_object* v_k_140_){
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
LEAN_EXPORT void l_Lean_Elab_elabAttr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_140_ = stack[0].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Lean_Elab_elabAttr___redArg___lam__0(v_k_140_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__0___boxed(lean_object* v_k_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Lean_Elab_elabAttr___redArg___lam__0(v_k_146_);
lean_dec(v_k_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
lean_object* l_Lean_Elab_elabAttr___redArg___lam__1(uint8_t v_attrKind_149_, lean_object* v_attrName_150_, lean_object* v_attr_151_, lean_object* v_toPure_152_, lean_object* v_____r_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_154_, 0, v_attrName_150_);
lean_ctor_set(v___x_154_, 1, v_attr_151_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*2, v_attrKind_149_);
v___x_155_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_Elab_elabAttr___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_attrKind_149_ = stack[0].m_num;
lean_object* v_attrName_150_ = stack[1].m_obj;
lean_object* v_attr_151_ = stack[2].m_obj;
lean_object* v_toPure_152_ = stack[3].m_obj;
lean_object* v_____r_153_ = stack[4].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Elab_elabAttr___redArg___lam__1(v_attrKind_149_, v_attrName_150_, v_attr_151_, v_toPure_152_, v_____r_153_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__1___boxed(lean_object* v_attrKind_157_, lean_object* v_attrName_158_, lean_object* v_attr_159_, lean_object* v_toPure_160_, lean_object* v_____r_161_){
_start:
{
uint8_t v_attrKind_boxed_162_; lean_object* v_res_163_; 
v_attrKind_boxed_162_ = lean_unbox(v_attrKind_157_);
v_res_163_ = l_Lean_Elab_elabAttr___redArg___lam__1(v_attrKind_boxed_162_, v_attrName_158_, v_attr_159_, v_toPure_160_, v_____r_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__2(lean_object* v___f_164_, lean_object* v_____r_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_apply_1(v___f_164_, v_____r_165_);
return v___x_166_;
}
}
lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_toMonadRef_171_, lean_object* v_inst_172_, lean_object* v_ref_173_, uint8_t v___x_174_, lean_object* v_toBind_175_, lean_object* v___f_176_, lean_object* v_____r_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_toMonadRef_171_, v_inst_172_, v_ref_173_, v___x_174_);
v___x_179_ = lean_apply_4(v_toBind_175_, lean_box(0), lean_box(0), v___x_178_, v___f_176_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Elab_elabAttr___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_167_ = stack[0].m_obj;
lean_object* v_inst_168_ = stack[1].m_obj;
lean_object* v_inst_169_ = stack[2].m_obj;
lean_object* v_inst_170_ = stack[3].m_obj;
lean_object* v_toMonadRef_171_ = stack[4].m_obj;
lean_object* v_inst_172_ = stack[5].m_obj;
lean_object* v_ref_173_ = stack[6].m_obj;
uint8_t v___x_174_ = stack[7].m_num;
lean_object* v_toBind_175_ = stack[8].m_obj;
lean_object* v___f_176_ = stack[9].m_obj;
lean_object* v_____r_177_ = stack[10].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_Elab_elabAttr___redArg___lam__3(v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_toMonadRef_171_, v_inst_172_, v_ref_173_, v___x_174_, v_toBind_175_, v___f_176_, v_____r_177_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3___boxed(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_toMonadRef_185_, lean_object* v_inst_186_, lean_object* v_ref_187_, lean_object* v___x_188_, lean_object* v_toBind_189_, lean_object* v___f_190_, lean_object* v_____r_191_){
_start:
{
uint8_t v___x_1197__boxed_192_; lean_object* v_res_193_; 
v___x_1197__boxed_192_ = lean_unbox(v___x_188_);
v_res_193_ = l_Lean_Elab_elabAttr___redArg___lam__3(v_inst_181_, v_inst_182_, v_inst_183_, v_inst_184_, v_toMonadRef_185_, v_inst_186_, v_ref_187_, v___x_1197__boxed_192_, v_toBind_189_, v___f_190_, v_____r_191_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__0));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__2));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__4));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__6));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object* v___f_206_, lean_object* v_val_207_, lean_object* v___x_208_, lean_object* v_attrName_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_toBind_212_, lean_object* v___f_213_, lean_object* v_env_214_){
_start:
{
lean_object* v___x_218_; lean_object* v_modules_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_218_ = l_Lean_Environment_header(v_env_214_);
v_modules_219_ = lean_ctor_get(v___x_218_, 3);
lean_inc_ref(v_modules_219_);
lean_dec_ref(v___x_218_);
v___x_220_ = lean_array_get_size(v_modules_219_);
v___x_221_ = lean_nat_dec_lt(v_val_207_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_modules_219_);
lean_dec(v___f_213_);
lean_dec(v_toBind_212_);
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_inst_210_);
lean_dec(v_attrName_209_);
goto v___jp_215_;
}
else
{
lean_object* v___x_222_; uint8_t v_hasData_223_; 
v___x_222_ = lean_array_fget_borrowed(v_modules_219_, v_val_207_);
v_hasData_223_ = lean_ctor_get_uint8(v___x_222_, sizeof(void*)*1 + 1);
if (v_hasData_223_ == 0)
{
lean_object* v___x_224_; lean_object* v_toImport_225_; lean_object* v_module_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v___f_206_);
v___x_224_ = lean_array_get(v___x_208_, v_modules_219_, v_val_207_);
lean_dec_ref(v_modules_219_);
v_toImport_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc_ref(v_toImport_225_);
lean_dec(v___x_224_);
v_module_226_ = lean_ctor_get(v_toImport_225_, 0);
lean_inc(v_module_226_);
lean_dec_ref(v_toImport_225_);
v___x_227_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1);
v___x_228_ = l_Lean_MessageData_ofName(v_attrName_209_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_MessageData_ofName(v_module_226_);
lean_inc_ref(v___x_232_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__5, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_232_);
v___x_237_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__7, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_throwError___redArg(v_inst_210_, v_inst_211_, v___x_238_);
v___x_240_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_239_, v___f_213_);
return v___x_240_;
}
else
{
lean_dec_ref(v_modules_219_);
lean_dec(v___f_213_);
lean_dec(v_toBind_212_);
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_inst_210_);
lean_dec(v_attrName_209_);
goto v___jp_215_;
}
}
v___jp_215_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_1(v___f_206_, v___x_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___boxed(lean_object* v___f_241_, lean_object* v_val_242_, lean_object* v___x_243_, lean_object* v_attrName_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_toBind_247_, lean_object* v___f_248_, lean_object* v_env_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Elab_elabAttr___redArg___lam__5(v___f_241_, v_val_242_, v___x_243_, v_attrName_244_, v_inst_245_, v_inst_246_, v_toBind_247_, v___f_248_, v_env_249_);
lean_dec_ref(v_env_249_);
lean_dec_ref(v___x_243_);
lean_dec(v_val_242_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object* v_ref_251_, lean_object* v___f_252_, lean_object* v___x_253_, lean_object* v_attrName_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_toBind_257_, lean_object* v___f_258_, lean_object* v_getEnv_259_, lean_object* v_____do__lift_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_260_, v_ref_251_);
if (lean_obj_tag(v___x_261_) == 1)
{
lean_object* v_val_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v_val_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v___x_261_, 1);
lean_inc(v_toBind_257_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_263_, 0, v___f_252_);
lean_closure_set(v___f_263_, 1, v_val_262_);
lean_closure_set(v___f_263_, 2, v___x_253_);
lean_closure_set(v___f_263_, 3, v_attrName_254_);
lean_closure_set(v___f_263_, 4, v_inst_255_);
lean_closure_set(v___f_263_, 5, v_inst_256_);
lean_closure_set(v___f_263_, 6, v_toBind_257_);
lean_closure_set(v___f_263_, 7, v___f_258_);
v___x_264_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v_getEnv_259_, v___f_263_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v___x_261_);
lean_dec(v_getEnv_259_);
lean_dec(v___f_258_);
lean_dec(v_toBind_257_);
lean_dec_ref(v_inst_256_);
lean_dec_ref(v_inst_255_);
lean_dec(v_attrName_254_);
lean_dec_ref(v___x_253_);
v___x_265_ = lean_box(0);
v___x_266_ = lean_apply_1(v___f_252_, v___x_265_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4___boxed(lean_object* v_ref_267_, lean_object* v___f_268_, lean_object* v___x_269_, lean_object* v_attrName_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_toBind_273_, lean_object* v___f_274_, lean_object* v_getEnv_275_, lean_object* v_____do__lift_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_elabAttr___redArg___lam__4(v_ref_267_, v___f_268_, v___x_269_, v_attrName_270_, v_inst_271_, v_inst_272_, v_toBind_273_, v___f_274_, v_getEnv_275_, v_____do__lift_276_);
lean_dec_ref(v_____do__lift_276_);
lean_dec(v_ref_267_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object* v_a_278_, lean_object* v___x_279_, lean_object* v___f_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_toMonadRef_285_, lean_object* v_inst_286_, lean_object* v_toBind_287_, lean_object* v___f_288_, lean_object* v___x_289_, lean_object* v_attrName_290_, lean_object* v_inst_291_, lean_object* v_getEnv_292_, lean_object* v_____do__lift_293_){
_start:
{
lean_object* v_toAttributeImplCore_294_; lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_toAttributeImplCore_294_ = lean_ctor_get(v_a_278_, 0);
lean_inc_ref(v_toAttributeImplCore_294_);
lean_dec_ref(v_a_278_);
v_ref_295_ = lean_ctor_get(v_toAttributeImplCore_294_, 0);
lean_inc_n(v_ref_295_, 2);
lean_dec_ref(v_toAttributeImplCore_294_);
v___x_296_ = l_Lean_regularInitAttr;
v___x_297_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_279_, v___x_296_, v_____do__lift_293_, v_ref_295_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_ref_295_);
lean_dec(v_getEnv_292_);
lean_dec_ref(v_inst_291_);
lean_dec(v_attrName_290_);
lean_dec_ref(v___x_289_);
lean_dec(v___f_288_);
lean_dec(v_toBind_287_);
lean_dec(v_inst_286_);
lean_dec_ref(v_toMonadRef_285_);
lean_dec_ref(v_inst_284_);
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
lean_dec_ref(v_inst_281_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v___f_280_, v___x_298_);
return v___x_299_;
}
else
{
uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___x_305_; 
lean_dec_ref_known(v___x_297_, 1);
lean_dec(v___f_280_);
v___x_300_ = 1;
v___x_301_ = lean_box(v___x_300_);
lean_inc_n(v_toBind_287_, 2);
lean_inc(v_ref_295_);
lean_inc_ref(v_inst_281_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_302_, 0, v_inst_281_);
lean_closure_set(v___f_302_, 1, v_inst_282_);
lean_closure_set(v___f_302_, 2, v_inst_283_);
lean_closure_set(v___f_302_, 3, v_inst_284_);
lean_closure_set(v___f_302_, 4, v_toMonadRef_285_);
lean_closure_set(v___f_302_, 5, v_inst_286_);
lean_closure_set(v___f_302_, 6, v_ref_295_);
lean_closure_set(v___f_302_, 7, v___x_301_);
lean_closure_set(v___f_302_, 8, v_toBind_287_);
lean_closure_set(v___f_302_, 9, v___f_288_);
lean_inc_ref(v___f_302_);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_303_, 0, v___f_302_);
lean_inc(v_getEnv_292_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_304_, 0, v_ref_295_);
lean_closure_set(v___f_304_, 1, v___f_302_);
lean_closure_set(v___f_304_, 2, v___x_289_);
lean_closure_set(v___f_304_, 3, v_attrName_290_);
lean_closure_set(v___f_304_, 4, v_inst_281_);
lean_closure_set(v___f_304_, 5, v_inst_291_);
lean_closure_set(v___f_304_, 6, v_toBind_287_);
lean_closure_set(v___f_304_, 7, v___f_303_);
lean_closure_set(v___f_304_, 8, v_getEnv_292_);
v___x_305_ = lean_apply_4(v_toBind_287_, lean_box(0), lean_box(0), v_getEnv_292_, v___f_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object* v_attrName_306_, lean_object* v___x_307_, lean_object* v___f_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_toMonadRef_313_, lean_object* v_inst_314_, lean_object* v_toBind_315_, lean_object* v___f_316_, lean_object* v___x_317_, lean_object* v_inst_318_, lean_object* v_getEnv_319_, lean_object* v_____do__lift_320_){
_start:
{
lean_object* v___x_321_; 
lean_inc(v_attrName_306_);
v___x_321_ = l_Lean_getAttributeImpl(v_____do__lift_320_, v_attrName_306_);
if (lean_obj_tag(v___x_321_) == 1)
{
lean_object* v_a_322_; lean_object* v___f_323_; lean_object* v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
lean_inc(v_getEnv_319_);
lean_inc(v_toBind_315_);
v___f_323_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__6), 16, 15);
lean_closure_set(v___f_323_, 0, v_a_322_);
lean_closure_set(v___f_323_, 1, v___x_307_);
lean_closure_set(v___f_323_, 2, v___f_308_);
lean_closure_set(v___f_323_, 3, v_inst_309_);
lean_closure_set(v___f_323_, 4, v_inst_310_);
lean_closure_set(v___f_323_, 5, v_inst_311_);
lean_closure_set(v___f_323_, 6, v_inst_312_);
lean_closure_set(v___f_323_, 7, v_toMonadRef_313_);
lean_closure_set(v___f_323_, 8, v_inst_314_);
lean_closure_set(v___f_323_, 9, v_toBind_315_);
lean_closure_set(v___f_323_, 10, v___f_316_);
lean_closure_set(v___f_323_, 11, v___x_317_);
lean_closure_set(v___f_323_, 12, v_attrName_306_);
lean_closure_set(v___f_323_, 13, v_inst_318_);
lean_closure_set(v___f_323_, 14, v_getEnv_319_);
v___x_324_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v_getEnv_319_, v___f_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v___x_321_);
lean_dec(v_getEnv_319_);
lean_dec_ref(v_inst_318_);
lean_dec_ref(v___x_317_);
lean_dec(v___f_316_);
lean_dec(v_toBind_315_);
lean_dec(v_inst_314_);
lean_dec_ref(v_toMonadRef_313_);
lean_dec_ref(v_inst_312_);
lean_dec_ref(v_inst_311_);
lean_dec_ref(v_inst_310_);
lean_dec_ref(v_inst_309_);
lean_dec(v___x_307_);
lean_dec(v_attrName_306_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_apply_1(v___f_308_, v___x_325_);
return v___x_326_;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__0));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__2));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object* v_attrName_333_, lean_object* v_toBind_334_, lean_object* v_getEnv_335_, lean_object* v___f_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_____do__lift_339_){
_start:
{
lean_object* v___x_340_; 
lean_inc(v_attrName_333_);
v___x_340_ = l_Lean_getAttributeImpl(v_____do__lift_339_, v_attrName_333_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_object* v___x_341_; 
lean_dec_ref_known(v___x_340_, 1);
lean_dec_ref(v_inst_338_);
lean_dec_ref(v_inst_337_);
lean_dec(v_attrName_333_);
v___x_341_ = lean_apply_4(v_toBind_334_, lean_box(0), lean_box(0), v_getEnv_335_, v___f_336_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec_ref(v___x_340_);
lean_dec(v___f_336_);
lean_dec(v_getEnv_335_);
lean_dec(v_toBind_334_);
v___x_342_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1);
v___x_343_ = l_Lean_MessageData_ofName(v_attrName_333_);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_throwError___redArg(v_inst_337_, v_inst_338_, v___x_346_);
return v___x_347_;
}
}
}
lean_object* l_Lean_Elab_elabAttr___redArg___lam__9(lean_object* v_inst_348_, uint8_t v_attrKind_349_, lean_object* v_attr_350_, lean_object* v_toPure_351_, lean_object* v___x_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_toMonadRef_356_, lean_object* v_inst_357_, lean_object* v_toBind_358_, lean_object* v___x_359_, lean_object* v_inst_360_, lean_object* v_attrName_361_){
_start:
{
lean_object* v_getEnv_362_; lean_object* v___x_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___f_367_; lean_object* v___x_368_; 
v_getEnv_362_ = lean_ctor_get(v_inst_348_, 0);
lean_inc_n(v_getEnv_362_, 3);
v___x_363_ = lean_box(v_attrKind_349_);
lean_inc_n(v_attrName_361_, 2);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_364_, 0, v___x_363_);
lean_closure_set(v___f_364_, 1, v_attrName_361_);
lean_closure_set(v___f_364_, 2, v_attr_350_);
lean_closure_set(v___f_364_, 3, v_toPure_351_);
lean_inc_ref(v___f_364_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_365_, 0, v___f_364_);
lean_inc_ref(v_inst_360_);
lean_inc_n(v_toBind_358_, 2);
lean_inc_ref(v_inst_353_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 15, 14);
lean_closure_set(v___f_366_, 0, v_attrName_361_);
lean_closure_set(v___f_366_, 1, v___x_352_);
lean_closure_set(v___f_366_, 2, v___f_364_);
lean_closure_set(v___f_366_, 3, v_inst_353_);
lean_closure_set(v___f_366_, 4, v_inst_348_);
lean_closure_set(v___f_366_, 5, v_inst_354_);
lean_closure_set(v___f_366_, 6, v_inst_355_);
lean_closure_set(v___f_366_, 7, v_toMonadRef_356_);
lean_closure_set(v___f_366_, 8, v_inst_357_);
lean_closure_set(v___f_366_, 9, v_toBind_358_);
lean_closure_set(v___f_366_, 10, v___f_365_);
lean_closure_set(v___f_366_, 11, v___x_359_);
lean_closure_set(v___f_366_, 12, v_inst_360_);
lean_closure_set(v___f_366_, 13, v_getEnv_362_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__8), 7, 6);
lean_closure_set(v___f_367_, 0, v_attrName_361_);
lean_closure_set(v___f_367_, 1, v_toBind_358_);
lean_closure_set(v___f_367_, 2, v_getEnv_362_);
lean_closure_set(v___f_367_, 3, v___f_366_);
lean_closure_set(v___f_367_, 4, v_inst_353_);
lean_closure_set(v___f_367_, 5, v_inst_360_);
v___x_368_ = lean_apply_4(v_toBind_358_, lean_box(0), lean_box(0), v_getEnv_362_, v___f_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Lean_Elab_elabAttr___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_348_ = stack[0].m_obj;
uint8_t v_attrKind_349_ = stack[1].m_num;
lean_object* v_attr_350_ = stack[2].m_obj;
lean_object* v_toPure_351_ = stack[3].m_obj;
lean_object* v___x_352_ = stack[4].m_obj;
lean_object* v_inst_353_ = stack[5].m_obj;
lean_object* v_inst_354_ = stack[6].m_obj;
lean_object* v_inst_355_ = stack[7].m_obj;
lean_object* v_toMonadRef_356_ = stack[8].m_obj;
lean_object* v_inst_357_ = stack[9].m_obj;
lean_object* v_toBind_358_ = stack[10].m_obj;
lean_object* v___x_359_ = stack[11].m_obj;
lean_object* v_inst_360_ = stack[12].m_obj;
lean_object* v_attrName_361_ = stack[13].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_Elab_elabAttr___redArg___lam__9(v_inst_348_, v_attrKind_349_, v_attr_350_, v_toPure_351_, v___x_352_, v_inst_353_, v_inst_354_, v_inst_355_, v_toMonadRef_356_, v_inst_357_, v_toBind_358_, v___x_359_, v_inst_360_, v_attrName_361_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9___boxed(lean_object* v_inst_370_, lean_object* v_attrKind_371_, lean_object* v_attr_372_, lean_object* v_toPure_373_, lean_object* v___x_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_toMonadRef_378_, lean_object* v_inst_379_, lean_object* v_toBind_380_, lean_object* v___x_381_, lean_object* v_inst_382_, lean_object* v_attrName_383_){
_start:
{
uint8_t v_attrKind_boxed_384_; lean_object* v_res_385_; 
v_attrKind_boxed_384_ = lean_unbox(v_attrKind_371_);
v_res_385_ = l_Lean_Elab_elabAttr___redArg___lam__9(v_inst_370_, v_attrKind_boxed_384_, v_attr_372_, v_toPure_373_, v___x_374_, v_inst_375_, v_inst_376_, v_inst_377_, v_toMonadRef_378_, v_inst_379_, v_toBind_380_, v___x_381_, v_inst_382_, v_attrName_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object* v___f_386_, lean_object* v_attrName_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_apply_1(v___f_386_, v_attrName_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__3));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
lean_object* l_Lean_Elab_elabAttr___redArg___lam__13(lean_object* v_inst_399_, uint8_t v_attrKind_400_, lean_object* v_toPure_401_, lean_object* v___x_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_toMonadRef_406_, lean_object* v_inst_407_, lean_object* v_toBind_408_, lean_object* v___x_409_, lean_object* v_inst_410_, lean_object* v___x_411_, lean_object* v_attr_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_413_ = lean_box(v_attrKind_400_);
lean_inc_ref(v_inst_410_);
lean_inc(v_toBind_408_);
lean_inc_ref(v_inst_403_);
lean_inc(v_toPure_401_);
lean_inc_n(v_attr_412_, 2);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_414_, 0, v_inst_399_);
lean_closure_set(v___f_414_, 1, v___x_413_);
lean_closure_set(v___f_414_, 2, v_attr_412_);
lean_closure_set(v___f_414_, 3, v_toPure_401_);
lean_closure_set(v___f_414_, 4, v___x_402_);
lean_closure_set(v___f_414_, 5, v_inst_403_);
lean_closure_set(v___f_414_, 6, v_inst_404_);
lean_closure_set(v___f_414_, 7, v_inst_405_);
lean_closure_set(v___f_414_, 8, v_toMonadRef_406_);
lean_closure_set(v___f_414_, 9, v_inst_407_);
lean_closure_set(v___f_414_, 10, v_toBind_408_);
lean_closure_set(v___f_414_, 11, v___x_409_);
lean_closure_set(v___f_414_, 12, v_inst_410_);
v___x_415_ = l_Lean_Syntax_getKind(v_attr_412_);
v___x_416_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2));
v___x_417_ = lean_name_eq(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
if (lean_obj_tag(v___x_415_) == 1)
{
lean_object* v_str_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_attr_412_);
lean_dec_ref(v_inst_410_);
lean_dec_ref(v_inst_403_);
v_str_418_ = lean_ctor_get(v___x_415_, 1);
lean_inc_ref(v_str_418_);
lean_dec_ref_known(v___x_415_, 2);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_419_, 0, v___f_414_);
v___x_420_ = lean_box(0);
v___x_421_ = l_Lean_Name_str___override(v___x_420_, v_str_418_);
v___x_422_ = lean_apply_2(v_toPure_401_, lean_box(0), v___x_421_);
v___x_423_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_422_, v___f_419_);
return v___x_423_;
}
else
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v___x_415_);
lean_dec(v_toPure_401_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_424_, 0, v___f_414_);
v___x_425_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__13___closed__4, &l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once, _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4);
v___x_426_ = l_Lean_throwErrorAt___redArg(v_inst_403_, v_inst_410_, v_attr_412_, v___x_425_);
v___x_427_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_426_, v___f_424_);
return v___x_427_;
}
}
else
{
lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v___x_415_);
lean_dec_ref(v_inst_410_);
lean_dec_ref(v_inst_403_);
v___f_428_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_428_, 0, v___f_414_);
v___x_429_ = l_Lean_Syntax_getArg(v_attr_412_, v___x_411_);
lean_dec(v_attr_412_);
v___x_430_ = l_Lean_Syntax_getId(v___x_429_);
lean_dec(v___x_429_);
v___x_431_ = l_Lean_Name_eraseMacroScopes(v___x_430_);
lean_dec(v___x_430_);
v___x_432_ = lean_apply_2(v_toPure_401_, lean_box(0), v___x_431_);
v___x_433_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_432_, v___f_428_);
return v___x_433_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_elabAttr___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_399_ = stack[0].m_obj;
uint8_t v_attrKind_400_ = stack[1].m_num;
lean_object* v_toPure_401_ = stack[2].m_obj;
lean_object* v___x_402_ = stack[3].m_obj;
lean_object* v_inst_403_ = stack[4].m_obj;
lean_object* v_inst_404_ = stack[5].m_obj;
lean_object* v_inst_405_ = stack[6].m_obj;
lean_object* v_toMonadRef_406_ = stack[7].m_obj;
lean_object* v_inst_407_ = stack[8].m_obj;
lean_object* v_toBind_408_ = stack[9].m_obj;
lean_object* v___x_409_ = stack[10].m_obj;
lean_object* v_inst_410_ = stack[11].m_obj;
lean_object* v___x_411_ = stack[12].m_obj;
lean_object* v_attr_412_ = stack[13].m_obj;
lean_object* v_res_434_;
v_res_434_ = l_Lean_Elab_elabAttr___redArg___lam__13(v_inst_399_, v_attrKind_400_, v_toPure_401_, v___x_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_toMonadRef_406_, v_inst_407_, v_toBind_408_, v___x_409_, v_inst_410_, v___x_411_, v_attr_412_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___boxed(lean_object* v_inst_435_, lean_object* v_attrKind_436_, lean_object* v_toPure_437_, lean_object* v___x_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_toMonadRef_442_, lean_object* v_inst_443_, lean_object* v_toBind_444_, lean_object* v___x_445_, lean_object* v_inst_446_, lean_object* v___x_447_, lean_object* v_attr_448_){
_start:
{
uint8_t v_attrKind_boxed_449_; lean_object* v_res_450_; 
v_attrKind_boxed_449_ = lean_unbox(v_attrKind_436_);
v_res_450_ = l_Lean_Elab_elabAttr___redArg___lam__13(v_inst_435_, v_attrKind_boxed_449_, v_toPure_437_, v___x_438_, v_inst_439_, v_inst_440_, v_inst_441_, v_toMonadRef_442_, v_inst_443_, v_toBind_444_, v___x_445_, v_inst_446_, v___x_447_, v_attr_448_);
lean_dec(v___x_447_);
return v_res_450_;
}
}
lean_object* l_Lean_Elab_elabAttr___redArg___lam__11(lean_object* v_inst_451_, lean_object* v_toPure_452_, lean_object* v___x_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_toMonadRef_457_, lean_object* v_inst_458_, lean_object* v_toBind_459_, lean_object* v___x_460_, lean_object* v_inst_461_, lean_object* v___x_462_, lean_object* v_attrInstance_463_, lean_object* v___f_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, uint8_t v_attrKind_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v_attr_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_469_ = lean_box(v_attrKind_468_);
lean_inc_ref(v_inst_461_);
lean_inc(v_toBind_459_);
lean_inc(v_inst_458_);
lean_inc_ref(v_inst_456_);
lean_inc_ref(v_inst_455_);
lean_inc_ref(v_inst_454_);
lean_inc_ref(v_inst_451_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__13___boxed), 14, 13);
lean_closure_set(v___f_470_, 0, v_inst_451_);
lean_closure_set(v___f_470_, 1, v___x_469_);
lean_closure_set(v___f_470_, 2, v_toPure_452_);
lean_closure_set(v___f_470_, 3, v___x_453_);
lean_closure_set(v___f_470_, 4, v_inst_454_);
lean_closure_set(v___f_470_, 5, v_inst_455_);
lean_closure_set(v___f_470_, 6, v_inst_456_);
lean_closure_set(v___f_470_, 7, v_toMonadRef_457_);
lean_closure_set(v___f_470_, 8, v_inst_458_);
lean_closure_set(v___f_470_, 9, v_toBind_459_);
lean_closure_set(v___f_470_, 10, v___x_460_);
lean_closure_set(v___f_470_, 11, v_inst_461_);
lean_closure_set(v___f_470_, 12, v___x_462_);
v___x_471_ = lean_unsigned_to_nat(1u);
v_attr_472_ = l_Lean_Syntax_getArg(v_attrInstance_463_, v___x_471_);
v___x_473_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_473_, 0, v_attr_472_);
lean_closure_set(v___x_473_, 1, v___f_464_);
v___x_474_ = l_Lean_Elab_liftMacroM___redArg(v_inst_454_, v_inst_465_, v_inst_451_, v_inst_466_, v_inst_461_, v_inst_467_, v_inst_455_, v_inst_456_, v_inst_458_, v___x_473_);
v___x_475_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_474_, v___f_470_);
return v___x_475_;
}
}
LEAN_EXPORT void l_Lean_Elab_elabAttr___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_451_ = stack[0].m_obj;
lean_object* v_toPure_452_ = stack[1].m_obj;
lean_object* v___x_453_ = stack[2].m_obj;
lean_object* v_inst_454_ = stack[3].m_obj;
lean_object* v_inst_455_ = stack[4].m_obj;
lean_object* v_inst_456_ = stack[5].m_obj;
lean_object* v_toMonadRef_457_ = stack[6].m_obj;
lean_object* v_inst_458_ = stack[7].m_obj;
lean_object* v_toBind_459_ = stack[8].m_obj;
lean_object* v___x_460_ = stack[9].m_obj;
lean_object* v_inst_461_ = stack[10].m_obj;
lean_object* v___x_462_ = stack[11].m_obj;
lean_object* v_attrInstance_463_ = stack[12].m_obj;
lean_object* v___f_464_ = stack[13].m_obj;
lean_object* v_inst_465_ = stack[14].m_obj;
lean_object* v_inst_466_ = stack[15].m_obj;
lean_object* v_inst_467_ = stack[16].m_obj;
uint8_t v_attrKind_468_ = stack[17].m_num;
lean_object* v_res_476_;
v_res_476_ = l_Lean_Elab_elabAttr___redArg___lam__11(v_inst_451_, v_toPure_452_, v___x_453_, v_inst_454_, v_inst_455_, v_inst_456_, v_toMonadRef_457_, v_inst_458_, v_toBind_459_, v___x_460_, v_inst_461_, v___x_462_, v_attrInstance_463_, v___f_464_, v_inst_465_, v_inst_466_, v_inst_467_, v_attrKind_468_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_477_ = _args[0];
lean_object* v_toPure_478_ = _args[1];
lean_object* v___x_479_ = _args[2];
lean_object* v_inst_480_ = _args[3];
lean_object* v_inst_481_ = _args[4];
lean_object* v_inst_482_ = _args[5];
lean_object* v_toMonadRef_483_ = _args[6];
lean_object* v_inst_484_ = _args[7];
lean_object* v_toBind_485_ = _args[8];
lean_object* v___x_486_ = _args[9];
lean_object* v_inst_487_ = _args[10];
lean_object* v___x_488_ = _args[11];
lean_object* v_attrInstance_489_ = _args[12];
lean_object* v___f_490_ = _args[13];
lean_object* v_inst_491_ = _args[14];
lean_object* v_inst_492_ = _args[15];
lean_object* v_inst_493_ = _args[16];
lean_object* v_attrKind_494_ = _args[17];
_start:
{
uint8_t v_attrKind_boxed_495_; lean_object* v_res_496_; 
v_attrKind_boxed_495_ = lean_unbox(v_attrKind_494_);
v_res_496_ = l_Lean_Elab_elabAttr___redArg___lam__11(v_inst_477_, v_toPure_478_, v___x_479_, v_inst_480_, v_inst_481_, v_inst_482_, v_toMonadRef_483_, v_inst_484_, v_toBind_485_, v___x_486_, v_inst_487_, v___x_488_, v_attrInstance_489_, v___f_490_, v_inst_491_, v_inst_492_, v_inst_493_, v_attrKind_boxed_495_);
lean_dec(v_attrInstance_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg(lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_attrInstance_508_){
_start:
{
lean_object* v_toApplicative_509_; lean_object* v_toBind_510_; lean_object* v_toPure_511_; lean_object* v_toMonadRef_512_; lean_object* v___f_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; 
v_toApplicative_509_ = lean_ctor_get(v_inst_498_, 0);
v_toBind_510_ = lean_ctor_get(v_inst_498_, 1);
v_toPure_511_ = lean_ctor_get(v_toApplicative_509_, 1);
v_toMonadRef_512_ = lean_ctor_get(v_inst_501_, 1);
lean_inc_ref(v_toMonadRef_512_);
v___f_513_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___closed__0));
v___x_514_ = lean_box(0);
v___x_515_ = l_Lean_instInhabitedEffectiveImport_default;
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_Syntax_getArg(v_attrInstance_508_, v___x_516_);
v___x_518_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_518_, 0, v___x_517_);
lean_inc(v_inst_506_);
lean_inc_ref(v_inst_505_);
lean_inc_ref(v_inst_504_);
lean_inc_ref(v_inst_500_);
lean_inc_ref(v_inst_501_);
lean_inc_ref(v_inst_503_);
lean_inc_ref_n(v_inst_499_, 2);
lean_inc_ref(v_inst_502_);
lean_inc_ref_n(v_inst_498_, 2);
v___x_519_ = l_Lean_Elab_liftMacroM___redArg(v_inst_498_, v_inst_502_, v_inst_499_, v_inst_503_, v_inst_501_, v_inst_500_, v_inst_504_, v_inst_505_, v_inst_506_, v___x_518_);
lean_inc_n(v_toBind_510_, 2);
lean_inc(v_toPure_511_);
v___f_520_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__11___boxed), 18, 17);
lean_closure_set(v___f_520_, 0, v_inst_499_);
lean_closure_set(v___f_520_, 1, v_toPure_511_);
lean_closure_set(v___f_520_, 2, v___x_514_);
lean_closure_set(v___f_520_, 3, v_inst_498_);
lean_closure_set(v___f_520_, 4, v_inst_504_);
lean_closure_set(v___f_520_, 5, v_inst_505_);
lean_closure_set(v___f_520_, 6, v_toMonadRef_512_);
lean_closure_set(v___f_520_, 7, v_inst_506_);
lean_closure_set(v___f_520_, 8, v_toBind_510_);
lean_closure_set(v___f_520_, 9, v___x_515_);
lean_closure_set(v___f_520_, 10, v_inst_501_);
lean_closure_set(v___f_520_, 11, v___x_516_);
lean_closure_set(v___f_520_, 12, v_attrInstance_508_);
lean_closure_set(v___f_520_, 13, v___f_513_);
lean_closure_set(v___f_520_, 14, v_inst_502_);
lean_closure_set(v___f_520_, 15, v_inst_503_);
lean_closure_set(v___f_520_, 16, v_inst_500_);
v___x_521_ = lean_apply_4(v_toBind_510_, lean_box(0), lean_box(0), v___x_519_, v___f_520_);
v___x_522_ = 1;
v___x_523_ = l_Lean_withoutExporting___redArg(v_inst_498_, v_inst_499_, v_inst_507_, v___x_521_, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr(lean_object* v_m_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_attrInstance_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Elab_elabAttr___redArg(v_inst_525_, v_inst_526_, v_inst_527_, v_inst_528_, v_inst_529_, v_inst_530_, v_inst_531_, v_inst_532_, v_inst_533_, v_inst_535_, v_attrInstance_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___boxed(lean_object* v_m_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_attrInstance_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Elab_elabAttr(v_m_538_, v_inst_539_, v_inst_540_, v_inst_541_, v_inst_542_, v_inst_543_, v_inst_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_inst_548_, v_inst_549_, v_attrInstance_550_);
lean_dec(v_inst_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0(lean_object* v_toPure_552_, lean_object* v_p_553_){
_start:
{
lean_object* v_snd_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_snd_554_ = lean_ctor_get(v_p_553_, 1);
lean_inc(v_snd_554_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_snd_554_);
v___x_556_ = lean_apply_2(v_toPure_552_, lean_box(0), v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(lean_object* v_toPure_557_, lean_object* v_p_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Elab_elabAttrs___redArg___lam__0(v_toPure_557_, v_p_558_);
lean_dec_ref(v_p_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1(lean_object* v_a_560_, lean_object* v_withRef_561_, lean_object* v___x_562_, lean_object* v_oldRef_563_){
_start:
{
lean_object* v_ref_564_; lean_object* v___x_565_; 
v_ref_564_ = l_Lean_replaceRef(v_a_560_, v_oldRef_563_);
v___x_565_ = lean_apply_3(v_withRef_561_, lean_box(0), v_ref_564_, v___x_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(lean_object* v_a_566_, lean_object* v_withRef_567_, lean_object* v___x_568_, lean_object* v_oldRef_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_elabAttrs___redArg___lam__1(v_a_566_, v_withRef_567_, v___x_568_, v_oldRef_569_);
lean_dec(v_oldRef_569_);
lean_dec(v_a_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__2(lean_object* v___y_571_, lean_object* v_toPure_572_, lean_object* v_____do__lift_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = lean_array_push(v___y_571_, v_____do__lift_573_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
v___x_577_ = lean_apply_2(v_toPure_572_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__3(lean_object* v___y_578_, lean_object* v_toPure_579_, lean_object* v_____r_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_____r_580_);
lean_ctor_set(v___x_581_, 1, v___y_578_);
v___x_582_ = lean_apply_2(v_toPure_579_, lean_box(0), v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__4(lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_toBind_588_, lean_object* v___f_589_, lean_object* v_ex_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Elab_logException___redArg(v_inst_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_ex_590_);
v___x_592_ = lean_apply_4(v_toBind_588_, lean_box(0), lean_box(0), v___x_591_, v___f_589_);
return v___x_592_;
}
}
lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5(lean_object* v_toMonadRef_593_, lean_object* v_toMonadExceptOf_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_toBind_605_, lean_object* v_toPure_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v___f_609_, lean_object* v_a_610_, lean_object* v_x_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_getRef_613_; lean_object* v_withRef_614_; lean_object* v_tryCatch_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_getRef_613_ = lean_ctor_get(v_toMonadRef_593_, 0);
lean_inc(v_getRef_613_);
v_withRef_614_ = lean_ctor_get(v_toMonadRef_593_, 1);
lean_inc(v_withRef_614_);
lean_dec_ref(v_toMonadRef_593_);
v_tryCatch_615_ = lean_ctor_get(v_toMonadExceptOf_594_, 1);
lean_inc(v_tryCatch_615_);
lean_dec_ref(v_toMonadExceptOf_594_);
lean_inc(v_a_610_);
lean_inc(v_inst_603_);
lean_inc_ref(v_inst_602_);
lean_inc_ref(v_inst_595_);
v___x_616_ = l_Lean_Elab_elabAttr___redArg(v_inst_595_, v_inst_596_, v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_a_610_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_617_, 0, v_a_610_);
lean_closure_set(v___f_617_, 1, v_withRef_614_);
lean_closure_set(v___f_617_, 2, v___x_616_);
lean_inc_n(v_toBind_605_, 3);
v___x_618_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v_getRef_613_, v___f_617_);
lean_inc(v_toPure_606_);
lean_inc_ref(v___y_612_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__2), 3, 2);
lean_closure_set(v___f_619_, 0, v___y_612_);
lean_closure_set(v___f_619_, 1, v_toPure_606_);
v___f_620_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__3), 3, 2);
lean_closure_set(v___f_620_, 0, v___y_612_);
lean_closure_set(v___f_620_, 1, v_toPure_606_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__4), 8, 7);
lean_closure_set(v___f_621_, 0, v_inst_595_);
lean_closure_set(v___f_621_, 1, v_inst_607_);
lean_closure_set(v___f_621_, 2, v_inst_603_);
lean_closure_set(v___f_621_, 3, v_inst_602_);
lean_closure_set(v___f_621_, 4, v_inst_608_);
lean_closure_set(v___f_621_, 5, v_toBind_605_);
lean_closure_set(v___f_621_, 6, v___f_620_);
v___x_622_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_618_, v___f_619_);
v___x_623_ = lean_apply_3(v_tryCatch_615_, lean_box(0), v___x_622_, v___f_621_);
v___x_624_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_623_, v___f_609_);
return v___x_624_;
}
}
LEAN_EXPORT void l_Lean_Elab_elabAttrs___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadRef_593_ = stack[0].m_obj;
lean_object* v_toMonadExceptOf_594_ = stack[1].m_obj;
lean_object* v_inst_595_ = stack[2].m_obj;
lean_object* v_inst_596_ = stack[3].m_obj;
lean_object* v_inst_597_ = stack[4].m_obj;
lean_object* v_inst_598_ = stack[5].m_obj;
lean_object* v_inst_599_ = stack[6].m_obj;
lean_object* v_inst_600_ = stack[7].m_obj;
lean_object* v_inst_601_ = stack[8].m_obj;
lean_object* v_inst_602_ = stack[9].m_obj;
lean_object* v_inst_603_ = stack[10].m_obj;
lean_object* v_inst_604_ = stack[11].m_obj;
lean_object* v_toBind_605_ = stack[12].m_obj;
lean_object* v_toPure_606_ = stack[13].m_obj;
lean_object* v_inst_607_ = stack[14].m_obj;
lean_object* v_inst_608_ = stack[15].m_obj;
lean_object* v___f_609_ = stack[16].m_obj;
lean_object* v_a_610_ = stack[17].m_obj;
lean_object* v___y_612_ = stack[19].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_Elab_elabAttrs___redArg___lam__5(v_toMonadRef_593_, v_toMonadExceptOf_594_, v_inst_595_, v_inst_596_, v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_toBind_605_, v_toPure_606_, v_inst_607_, v_inst_608_, v___f_609_, v_a_610_, lean_box(0), v___y_612_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toMonadRef_626_ = _args[0];
lean_object* v_toMonadExceptOf_627_ = _args[1];
lean_object* v_inst_628_ = _args[2];
lean_object* v_inst_629_ = _args[3];
lean_object* v_inst_630_ = _args[4];
lean_object* v_inst_631_ = _args[5];
lean_object* v_inst_632_ = _args[6];
lean_object* v_inst_633_ = _args[7];
lean_object* v_inst_634_ = _args[8];
lean_object* v_inst_635_ = _args[9];
lean_object* v_inst_636_ = _args[10];
lean_object* v_inst_637_ = _args[11];
lean_object* v_toBind_638_ = _args[12];
lean_object* v_toPure_639_ = _args[13];
lean_object* v_inst_640_ = _args[14];
lean_object* v_inst_641_ = _args[15];
lean_object* v___f_642_ = _args[16];
lean_object* v_a_643_ = _args[17];
lean_object* v_x_644_ = _args[18];
lean_object* v___y_645_ = _args[19];
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_elabAttrs___redArg___lam__5(v_toMonadRef_626_, v_toMonadExceptOf_627_, v_inst_628_, v_inst_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_inst_635_, v_inst_636_, v_inst_637_, v_toBind_638_, v_toPure_639_, v_inst_640_, v_inst_641_, v___f_642_, v_a_643_, v_x_644_, v___y_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__6(lean_object* v_toPure_647_, lean_object* v_____s_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_apply_2(v_toPure_647_, lean_box(0), v_____s_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg(lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_attrInstances_664_){
_start:
{
lean_object* v_toApplicative_665_; lean_object* v_toBind_666_; lean_object* v_toMonadExceptOf_667_; lean_object* v_toMonadRef_668_; lean_object* v_toPure_669_; lean_object* v_attrs_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_toApplicative_665_ = lean_ctor_get(v_inst_652_, 0);
v_toBind_666_ = lean_ctor_get(v_inst_652_, 1);
lean_inc_n(v_toBind_666_, 2);
v_toMonadExceptOf_667_ = lean_ctor_get(v_inst_655_, 0);
lean_inc_ref(v_toMonadExceptOf_667_);
v_toMonadRef_668_ = lean_ctor_get(v_inst_655_, 1);
lean_inc_ref(v_toMonadRef_668_);
v_toPure_669_ = lean_ctor_get(v_toApplicative_665_, 1);
v_attrs_670_ = ((lean_object*)(l_Lean_Elab_elabAttrs___redArg___closed__0));
lean_inc_n(v_toPure_669_, 3);
v___f_671_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_671_, 0, v_toPure_669_);
lean_inc_ref(v_inst_652_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__5___boxed), 20, 17);
lean_closure_set(v___f_672_, 0, v_toMonadRef_668_);
lean_closure_set(v___f_672_, 1, v_toMonadExceptOf_667_);
lean_closure_set(v___f_672_, 2, v_inst_652_);
lean_closure_set(v___f_672_, 3, v_inst_653_);
lean_closure_set(v___f_672_, 4, v_inst_654_);
lean_closure_set(v___f_672_, 5, v_inst_655_);
lean_closure_set(v___f_672_, 6, v_inst_656_);
lean_closure_set(v___f_672_, 7, v_inst_657_);
lean_closure_set(v___f_672_, 8, v_inst_658_);
lean_closure_set(v___f_672_, 9, v_inst_659_);
lean_closure_set(v___f_672_, 10, v_inst_660_);
lean_closure_set(v___f_672_, 11, v_inst_663_);
lean_closure_set(v___f_672_, 12, v_toBind_666_);
lean_closure_set(v___f_672_, 13, v_toPure_669_);
lean_closure_set(v___f_672_, 14, v_inst_661_);
lean_closure_set(v___f_672_, 15, v_inst_662_);
lean_closure_set(v___f_672_, 16, v___f_671_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__6), 2, 1);
lean_closure_set(v___f_673_, 0, v_toPure_669_);
v_sz_674_ = lean_array_size(v_attrInstances_664_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_652_, v_attrInstances_664_, v___f_672_, v_sz_674_, v___x_675_, v_attrs_670_);
v___x_677_ = lean_apply_4(v_toBind_666_, lean_box(0), lean_box(0), v___x_676_, v___f_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs(lean_object* v_m_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_attrInstances_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Elab_elabAttrs___redArg(v_inst_679_, v_inst_680_, v_inst_681_, v_inst_682_, v_inst_683_, v_inst_684_, v_inst_685_, v_inst_686_, v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_attrInstances_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_stx_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = l_Lean_Syntax_getArg(v_stx_705_, v___x_706_);
v___x_708_ = l_Lean_Syntax_getSepArgs(v___x_707_);
lean_dec(v___x_707_);
v___x_709_ = l_Lean_Elab_elabAttrs___redArg(v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_inst_699_, v_inst_700_, v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___boxed(lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_stx_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_710_, v_inst_711_, v_inst_712_, v_inst_713_, v_inst_714_, v_inst_715_, v_inst_716_, v_inst_717_, v_inst_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_stx_722_);
lean_dec(v_stx_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* v_m_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_stx_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_725_, v_inst_726_, v_inst_727_, v_inst_728_, v_inst_729_, v_inst_730_, v_inst_731_, v_inst_732_, v_inst_733_, v_inst_734_, v_inst_735_, v_inst_736_, v_stx_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___boxed(lean_object* v_m_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_stx_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_elabDeclAttrs(v_m_739_, v_inst_740_, v_inst_741_, v_inst_742_, v_inst_743_, v_inst_744_, v_inst_745_, v_inst_746_, v_inst_747_, v_inst_748_, v_inst_749_, v_inst_750_, v_inst_751_, v_stx_752_);
lean_dec(v_stx_752_);
return v_res_753_;
}
}
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
