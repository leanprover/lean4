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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_toMonadRef_169_, lean_object* v_inst_170_, lean_object* v_ref_171_, uint8_t v___x_172_, lean_object* v_toBind_173_, lean_object* v___f_174_, lean_object* v_____r_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_165_, v_inst_166_, v_inst_167_, v_inst_168_, v_toMonadRef_169_, v_inst_170_, v_ref_171_, v___x_172_);
v___x_177_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v___x_176_, v___f_174_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3___boxed(lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_toMonadRef_182_, lean_object* v_inst_183_, lean_object* v_ref_184_, lean_object* v___x_185_, lean_object* v_toBind_186_, lean_object* v___f_187_, lean_object* v_____r_188_){
_start:
{
uint8_t v___x_1172__boxed_189_; lean_object* v_res_190_; 
v___x_1172__boxed_189_ = lean_unbox(v___x_185_);
v_res_190_ = l_Lean_Elab_elabAttr___redArg___lam__3(v_inst_178_, v_inst_179_, v_inst_180_, v_inst_181_, v_toMonadRef_182_, v_inst_183_, v_ref_184_, v___x_1172__boxed_189_, v_toBind_186_, v___f_187_, v_____r_188_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__0));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__2));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__4));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__6));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object* v___f_203_, lean_object* v_val_204_, lean_object* v___x_205_, lean_object* v_attrName_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_toBind_209_, lean_object* v___f_210_, lean_object* v_env_211_){
_start:
{
lean_object* v___x_215_; lean_object* v_modules_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_215_ = l_Lean_Environment_header(v_env_211_);
v_modules_216_ = lean_ctor_get(v___x_215_, 3);
lean_inc_ref(v_modules_216_);
lean_dec_ref(v___x_215_);
v___x_217_ = lean_array_get_size(v_modules_216_);
v___x_218_ = lean_nat_dec_lt(v_val_204_, v___x_217_);
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
v___x_219_ = lean_array_fget_borrowed(v_modules_216_, v_val_204_);
v_hasData_220_ = lean_ctor_get_uint8(v___x_219_, sizeof(void*)*1 + 1);
if (v_hasData_220_ == 0)
{
lean_object* v___x_221_; lean_object* v_toImport_222_; lean_object* v_module_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___f_203_);
v___x_221_ = lean_array_get(v___x_205_, v_modules_216_, v_val_204_);
lean_dec_ref(v_modules_216_);
v_toImport_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_ref(v_toImport_222_);
lean_dec(v___x_221_);
v_module_223_ = lean_ctor_get(v_toImport_222_, 0);
lean_inc(v_module_223_);
lean_dec_ref(v_toImport_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1);
v___x_225_ = l_Lean_MessageData_ofName(v_attrName_206_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = l_Lean_MessageData_ofName(v_module_223_);
lean_inc_ref(v___x_229_);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__5, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_229_);
v___x_234_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__7, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_throwError___redArg(v_inst_207_, v_inst_208_, v___x_235_);
v___x_237_ = lean_apply_4(v_toBind_209_, lean_box(0), lean_box(0), v___x_236_, v___f_210_);
return v___x_237_;
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
v___x_214_ = lean_apply_1(v___f_203_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___boxed(lean_object* v___f_238_, lean_object* v_val_239_, lean_object* v___x_240_, lean_object* v_attrName_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_toBind_244_, lean_object* v___f_245_, lean_object* v_env_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_elabAttr___redArg___lam__5(v___f_238_, v_val_239_, v___x_240_, v_attrName_241_, v_inst_242_, v_inst_243_, v_toBind_244_, v___f_245_, v_env_246_);
lean_dec_ref(v_env_246_);
lean_dec_ref(v___x_240_);
lean_dec(v_val_239_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object* v_ref_248_, lean_object* v___f_249_, lean_object* v___x_250_, lean_object* v_attrName_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_toBind_254_, lean_object* v___f_255_, lean_object* v_getEnv_256_, lean_object* v_____do__lift_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_257_, v_ref_248_);
if (lean_obj_tag(v___x_258_) == 1)
{
lean_object* v_val_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v___x_258_, 1);
lean_inc(v_toBind_254_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_260_, 0, v___f_249_);
lean_closure_set(v___f_260_, 1, v_val_259_);
lean_closure_set(v___f_260_, 2, v___x_250_);
lean_closure_set(v___f_260_, 3, v_attrName_251_);
lean_closure_set(v___f_260_, 4, v_inst_252_);
lean_closure_set(v___f_260_, 5, v_inst_253_);
lean_closure_set(v___f_260_, 6, v_toBind_254_);
lean_closure_set(v___f_260_, 7, v___f_255_);
v___x_261_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v_getEnv_256_, v___f_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v___x_258_);
lean_dec(v_getEnv_256_);
lean_dec(v___f_255_);
lean_dec(v_toBind_254_);
lean_dec_ref(v_inst_253_);
lean_dec_ref(v_inst_252_);
lean_dec(v_attrName_251_);
lean_dec_ref(v___x_250_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_apply_1(v___f_249_, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4___boxed(lean_object* v_ref_264_, lean_object* v___f_265_, lean_object* v___x_266_, lean_object* v_attrName_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_toBind_270_, lean_object* v___f_271_, lean_object* v_getEnv_272_, lean_object* v_____do__lift_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_elabAttr___redArg___lam__4(v_ref_264_, v___f_265_, v___x_266_, v_attrName_267_, v_inst_268_, v_inst_269_, v_toBind_270_, v___f_271_, v_getEnv_272_, v_____do__lift_273_);
lean_dec_ref(v_____do__lift_273_);
lean_dec(v_ref_264_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object* v_a_275_, lean_object* v___x_276_, lean_object* v___f_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_toMonadRef_282_, lean_object* v_inst_283_, lean_object* v_toBind_284_, lean_object* v___f_285_, lean_object* v___x_286_, lean_object* v_attrName_287_, lean_object* v_inst_288_, lean_object* v_getEnv_289_, lean_object* v_____do__lift_290_){
_start:
{
lean_object* v_toAttributeImplCore_291_; lean_object* v_ref_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_toAttributeImplCore_291_ = lean_ctor_get(v_a_275_, 0);
lean_inc_ref(v_toAttributeImplCore_291_);
lean_dec_ref(v_a_275_);
v_ref_292_ = lean_ctor_get(v_toAttributeImplCore_291_, 0);
lean_inc_n(v_ref_292_, 2);
lean_dec_ref(v_toAttributeImplCore_291_);
v___x_293_ = l_Lean_regularInitAttr;
v___x_294_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_276_, v___x_293_, v_____do__lift_290_, v_ref_292_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_ref_292_);
lean_dec(v_getEnv_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_attrName_287_);
lean_dec_ref(v___x_286_);
lean_dec(v___f_285_);
lean_dec(v_toBind_284_);
lean_dec(v_inst_283_);
lean_dec_ref(v_toMonadRef_282_);
lean_dec(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec_ref(v_inst_279_);
lean_dec_ref(v_inst_278_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_apply_1(v___f_277_, v___x_295_);
return v___x_296_;
}
else
{
uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___f_300_; lean_object* v___f_301_; lean_object* v___x_302_; 
lean_dec_ref_known(v___x_294_, 1);
lean_dec(v___f_277_);
v___x_297_ = 1;
v___x_298_ = lean_box(v___x_297_);
lean_inc_n(v_toBind_284_, 2);
lean_inc(v_ref_292_);
lean_inc_ref(v_inst_278_);
v___f_299_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_299_, 0, v_inst_278_);
lean_closure_set(v___f_299_, 1, v_inst_279_);
lean_closure_set(v___f_299_, 2, v_inst_280_);
lean_closure_set(v___f_299_, 3, v_inst_281_);
lean_closure_set(v___f_299_, 4, v_toMonadRef_282_);
lean_closure_set(v___f_299_, 5, v_inst_283_);
lean_closure_set(v___f_299_, 6, v_ref_292_);
lean_closure_set(v___f_299_, 7, v___x_298_);
lean_closure_set(v___f_299_, 8, v_toBind_284_);
lean_closure_set(v___f_299_, 9, v___f_285_);
lean_inc_ref(v___f_299_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_300_, 0, v___f_299_);
lean_inc(v_getEnv_289_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_301_, 0, v_ref_292_);
lean_closure_set(v___f_301_, 1, v___f_299_);
lean_closure_set(v___f_301_, 2, v___x_286_);
lean_closure_set(v___f_301_, 3, v_attrName_287_);
lean_closure_set(v___f_301_, 4, v_inst_278_);
lean_closure_set(v___f_301_, 5, v_inst_288_);
lean_closure_set(v___f_301_, 6, v_toBind_284_);
lean_closure_set(v___f_301_, 7, v___f_300_);
lean_closure_set(v___f_301_, 8, v_getEnv_289_);
v___x_302_ = lean_apply_4(v_toBind_284_, lean_box(0), lean_box(0), v_getEnv_289_, v___f_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object* v_attrName_303_, lean_object* v___x_304_, lean_object* v___f_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_toMonadRef_310_, lean_object* v_inst_311_, lean_object* v_toBind_312_, lean_object* v___f_313_, lean_object* v___x_314_, lean_object* v_inst_315_, lean_object* v_getEnv_316_, lean_object* v_____do__lift_317_){
_start:
{
lean_object* v___x_318_; 
lean_inc(v_attrName_303_);
v___x_318_ = l_Lean_getAttributeImpl(v_____do__lift_317_, v_attrName_303_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_a_319_; lean_object* v___f_320_; lean_object* v___x_321_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
lean_inc(v_getEnv_316_);
lean_inc(v_toBind_312_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__6), 16, 15);
lean_closure_set(v___f_320_, 0, v_a_319_);
lean_closure_set(v___f_320_, 1, v___x_304_);
lean_closure_set(v___f_320_, 2, v___f_305_);
lean_closure_set(v___f_320_, 3, v_inst_306_);
lean_closure_set(v___f_320_, 4, v_inst_307_);
lean_closure_set(v___f_320_, 5, v_inst_308_);
lean_closure_set(v___f_320_, 6, v_inst_309_);
lean_closure_set(v___f_320_, 7, v_toMonadRef_310_);
lean_closure_set(v___f_320_, 8, v_inst_311_);
lean_closure_set(v___f_320_, 9, v_toBind_312_);
lean_closure_set(v___f_320_, 10, v___f_313_);
lean_closure_set(v___f_320_, 11, v___x_314_);
lean_closure_set(v___f_320_, 12, v_attrName_303_);
lean_closure_set(v___f_320_, 13, v_inst_315_);
lean_closure_set(v___f_320_, 14, v_getEnv_316_);
v___x_321_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v_getEnv_316_, v___f_320_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v___x_318_);
lean_dec(v_getEnv_316_);
lean_dec_ref(v_inst_315_);
lean_dec_ref(v___x_314_);
lean_dec(v___f_313_);
lean_dec(v_toBind_312_);
lean_dec(v_inst_311_);
lean_dec_ref(v_toMonadRef_310_);
lean_dec(v_inst_309_);
lean_dec_ref(v_inst_308_);
lean_dec_ref(v_inst_307_);
lean_dec_ref(v_inst_306_);
lean_dec(v___x_304_);
lean_dec(v_attrName_303_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_apply_1(v___f_305_, v___x_322_);
return v___x_323_;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__0));
v___x_326_ = l_Lean_stringToMessageData(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__2));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object* v_attrName_330_, lean_object* v_toBind_331_, lean_object* v_getEnv_332_, lean_object* v___f_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_____do__lift_336_){
_start:
{
lean_object* v___x_337_; 
lean_inc(v_attrName_330_);
v___x_337_ = l_Lean_getAttributeImpl(v_____do__lift_336_, v_attrName_330_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v___x_338_; 
lean_dec_ref_known(v___x_337_, 1);
lean_dec_ref(v_inst_335_);
lean_dec_ref(v_inst_334_);
lean_dec(v_attrName_330_);
v___x_338_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v_getEnv_332_, v___f_333_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref(v___x_337_);
lean_dec(v___f_333_);
lean_dec(v_getEnv_332_);
lean_dec(v_toBind_331_);
v___x_339_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1);
v___x_340_ = l_Lean_MessageData_ofName(v_attrName_330_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_throwError___redArg(v_inst_334_, v_inst_335_, v___x_343_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9(lean_object* v_inst_345_, uint8_t v_attrKind_346_, lean_object* v_attr_347_, lean_object* v_toPure_348_, lean_object* v___x_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_toMonadRef_353_, lean_object* v_inst_354_, lean_object* v_toBind_355_, lean_object* v___x_356_, lean_object* v_inst_357_, lean_object* v_attrName_358_){
_start:
{
lean_object* v_getEnv_359_; lean_object* v___x_360_; lean_object* v___f_361_; lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___f_364_; lean_object* v___x_365_; 
v_getEnv_359_ = lean_ctor_get(v_inst_345_, 0);
lean_inc_n(v_getEnv_359_, 3);
v___x_360_ = lean_box(v_attrKind_346_);
lean_inc_n(v_attrName_358_, 2);
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_361_, 0, v___x_360_);
lean_closure_set(v___f_361_, 1, v_attrName_358_);
lean_closure_set(v___f_361_, 2, v_attr_347_);
lean_closure_set(v___f_361_, 3, v_toPure_348_);
lean_inc_ref(v___f_361_);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_362_, 0, v___f_361_);
lean_inc_ref(v_inst_357_);
lean_inc_n(v_toBind_355_, 2);
lean_inc_ref(v_inst_350_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 15, 14);
lean_closure_set(v___f_363_, 0, v_attrName_358_);
lean_closure_set(v___f_363_, 1, v___x_349_);
lean_closure_set(v___f_363_, 2, v___f_361_);
lean_closure_set(v___f_363_, 3, v_inst_350_);
lean_closure_set(v___f_363_, 4, v_inst_345_);
lean_closure_set(v___f_363_, 5, v_inst_351_);
lean_closure_set(v___f_363_, 6, v_inst_352_);
lean_closure_set(v___f_363_, 7, v_toMonadRef_353_);
lean_closure_set(v___f_363_, 8, v_inst_354_);
lean_closure_set(v___f_363_, 9, v_toBind_355_);
lean_closure_set(v___f_363_, 10, v___f_362_);
lean_closure_set(v___f_363_, 11, v___x_356_);
lean_closure_set(v___f_363_, 12, v_inst_357_);
lean_closure_set(v___f_363_, 13, v_getEnv_359_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__8), 7, 6);
lean_closure_set(v___f_364_, 0, v_attrName_358_);
lean_closure_set(v___f_364_, 1, v_toBind_355_);
lean_closure_set(v___f_364_, 2, v_getEnv_359_);
lean_closure_set(v___f_364_, 3, v___f_363_);
lean_closure_set(v___f_364_, 4, v_inst_350_);
lean_closure_set(v___f_364_, 5, v_inst_357_);
v___x_365_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v_getEnv_359_, v___f_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9___boxed(lean_object* v_inst_366_, lean_object* v_attrKind_367_, lean_object* v_attr_368_, lean_object* v_toPure_369_, lean_object* v___x_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_toMonadRef_374_, lean_object* v_inst_375_, lean_object* v_toBind_376_, lean_object* v___x_377_, lean_object* v_inst_378_, lean_object* v_attrName_379_){
_start:
{
uint8_t v_attrKind_boxed_380_; lean_object* v_res_381_; 
v_attrKind_boxed_380_ = lean_unbox(v_attrKind_367_);
v_res_381_ = l_Lean_Elab_elabAttr___redArg___lam__9(v_inst_366_, v_attrKind_boxed_380_, v_attr_368_, v_toPure_369_, v___x_370_, v_inst_371_, v_inst_372_, v_inst_373_, v_toMonadRef_374_, v_inst_375_, v_toBind_376_, v___x_377_, v_inst_378_, v_attrName_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object* v___f_382_, lean_object* v_attrName_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_apply_1(v___f_382_, v_attrName_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__3));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13(lean_object* v_inst_395_, uint8_t v_attrKind_396_, lean_object* v_toPure_397_, lean_object* v___x_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_toMonadRef_402_, lean_object* v_inst_403_, lean_object* v_toBind_404_, lean_object* v___x_405_, lean_object* v_inst_406_, lean_object* v___x_407_, lean_object* v_attr_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_409_ = lean_box(v_attrKind_396_);
lean_inc_ref(v_inst_406_);
lean_inc(v_toBind_404_);
lean_inc_ref(v_inst_399_);
lean_inc(v_toPure_397_);
lean_inc_n(v_attr_408_, 2);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_410_, 0, v_inst_395_);
lean_closure_set(v___f_410_, 1, v___x_409_);
lean_closure_set(v___f_410_, 2, v_attr_408_);
lean_closure_set(v___f_410_, 3, v_toPure_397_);
lean_closure_set(v___f_410_, 4, v___x_398_);
lean_closure_set(v___f_410_, 5, v_inst_399_);
lean_closure_set(v___f_410_, 6, v_inst_400_);
lean_closure_set(v___f_410_, 7, v_inst_401_);
lean_closure_set(v___f_410_, 8, v_toMonadRef_402_);
lean_closure_set(v___f_410_, 9, v_inst_403_);
lean_closure_set(v___f_410_, 10, v_toBind_404_);
lean_closure_set(v___f_410_, 11, v___x_405_);
lean_closure_set(v___f_410_, 12, v_inst_406_);
v___x_411_ = l_Lean_Syntax_getKind(v_attr_408_);
v___x_412_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2));
v___x_413_ = lean_name_eq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
if (lean_obj_tag(v___x_411_) == 1)
{
lean_object* v_str_414_; lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_attr_408_);
lean_dec_ref(v_inst_406_);
lean_dec_ref(v_inst_399_);
v_str_414_ = lean_ctor_get(v___x_411_, 1);
lean_inc_ref(v_str_414_);
lean_dec_ref_known(v___x_411_, 2);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_415_, 0, v___f_410_);
v___x_416_ = lean_box(0);
v___x_417_ = l_Lean_Name_str___override(v___x_416_, v_str_414_);
v___x_418_ = lean_apply_2(v_toPure_397_, lean_box(0), v___x_417_);
v___x_419_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v___x_418_, v___f_415_);
return v___x_419_;
}
else
{
lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v___x_411_);
lean_dec(v_toPure_397_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_420_, 0, v___f_410_);
v___x_421_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__13___closed__4, &l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once, _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4);
v___x_422_ = l_Lean_throwErrorAt___redArg(v_inst_399_, v_inst_406_, v_attr_408_, v___x_421_);
v___x_423_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v___x_422_, v___f_420_);
return v___x_423_;
}
}
else
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v___x_411_);
lean_dec_ref(v_inst_406_);
lean_dec_ref(v_inst_399_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_424_, 0, v___f_410_);
v___x_425_ = l_Lean_Syntax_getArg(v_attr_408_, v___x_407_);
lean_dec(v_attr_408_);
v___x_426_ = l_Lean_Syntax_getId(v___x_425_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_Name_eraseMacroScopes(v___x_426_);
lean_dec(v___x_426_);
v___x_428_ = lean_apply_2(v_toPure_397_, lean_box(0), v___x_427_);
v___x_429_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v___x_428_, v___f_424_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___boxed(lean_object* v_inst_430_, lean_object* v_attrKind_431_, lean_object* v_toPure_432_, lean_object* v___x_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_toMonadRef_437_, lean_object* v_inst_438_, lean_object* v_toBind_439_, lean_object* v___x_440_, lean_object* v_inst_441_, lean_object* v___x_442_, lean_object* v_attr_443_){
_start:
{
uint8_t v_attrKind_boxed_444_; lean_object* v_res_445_; 
v_attrKind_boxed_444_ = lean_unbox(v_attrKind_431_);
v_res_445_ = l_Lean_Elab_elabAttr___redArg___lam__13(v_inst_430_, v_attrKind_boxed_444_, v_toPure_432_, v___x_433_, v_inst_434_, v_inst_435_, v_inst_436_, v_toMonadRef_437_, v_inst_438_, v_toBind_439_, v___x_440_, v_inst_441_, v___x_442_, v_attr_443_);
lean_dec(v___x_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11(lean_object* v_inst_446_, lean_object* v_toPure_447_, lean_object* v___x_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_toMonadRef_452_, lean_object* v_inst_453_, lean_object* v_toBind_454_, lean_object* v___x_455_, lean_object* v_inst_456_, lean_object* v___x_457_, lean_object* v_attrInstance_458_, lean_object* v___f_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, uint8_t v_attrKind_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___f_465_; lean_object* v___x_466_; lean_object* v_attr_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_464_ = lean_box(v_attrKind_463_);
lean_inc_ref(v_inst_456_);
lean_inc(v_toBind_454_);
lean_inc(v_inst_453_);
lean_inc(v_inst_451_);
lean_inc_ref(v_inst_450_);
lean_inc_ref(v_inst_449_);
lean_inc_ref(v_inst_446_);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__13___boxed), 14, 13);
lean_closure_set(v___f_465_, 0, v_inst_446_);
lean_closure_set(v___f_465_, 1, v___x_464_);
lean_closure_set(v___f_465_, 2, v_toPure_447_);
lean_closure_set(v___f_465_, 3, v___x_448_);
lean_closure_set(v___f_465_, 4, v_inst_449_);
lean_closure_set(v___f_465_, 5, v_inst_450_);
lean_closure_set(v___f_465_, 6, v_inst_451_);
lean_closure_set(v___f_465_, 7, v_toMonadRef_452_);
lean_closure_set(v___f_465_, 8, v_inst_453_);
lean_closure_set(v___f_465_, 9, v_toBind_454_);
lean_closure_set(v___f_465_, 10, v___x_455_);
lean_closure_set(v___f_465_, 11, v_inst_456_);
lean_closure_set(v___f_465_, 12, v___x_457_);
v___x_466_ = lean_unsigned_to_nat(1u);
v_attr_467_ = l_Lean_Syntax_getArg(v_attrInstance_458_, v___x_466_);
v___x_468_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_468_, 0, v_attr_467_);
lean_closure_set(v___x_468_, 1, v___f_459_);
v___x_469_ = l_Lean_Elab_liftMacroM___redArg(v_inst_449_, v_inst_460_, v_inst_446_, v_inst_461_, v_inst_456_, v_inst_462_, v_inst_450_, v_inst_451_, v_inst_453_, v___x_468_);
v___x_470_ = lean_apply_4(v_toBind_454_, lean_box(0), lean_box(0), v___x_469_, v___f_465_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_471_ = _args[0];
lean_object* v_toPure_472_ = _args[1];
lean_object* v___x_473_ = _args[2];
lean_object* v_inst_474_ = _args[3];
lean_object* v_inst_475_ = _args[4];
lean_object* v_inst_476_ = _args[5];
lean_object* v_toMonadRef_477_ = _args[6];
lean_object* v_inst_478_ = _args[7];
lean_object* v_toBind_479_ = _args[8];
lean_object* v___x_480_ = _args[9];
lean_object* v_inst_481_ = _args[10];
lean_object* v___x_482_ = _args[11];
lean_object* v_attrInstance_483_ = _args[12];
lean_object* v___f_484_ = _args[13];
lean_object* v_inst_485_ = _args[14];
lean_object* v_inst_486_ = _args[15];
lean_object* v_inst_487_ = _args[16];
lean_object* v_attrKind_488_ = _args[17];
_start:
{
uint8_t v_attrKind_boxed_489_; lean_object* v_res_490_; 
v_attrKind_boxed_489_ = lean_unbox(v_attrKind_488_);
v_res_490_ = l_Lean_Elab_elabAttr___redArg___lam__11(v_inst_471_, v_toPure_472_, v___x_473_, v_inst_474_, v_inst_475_, v_inst_476_, v_toMonadRef_477_, v_inst_478_, v_toBind_479_, v___x_480_, v_inst_481_, v___x_482_, v_attrInstance_483_, v___f_484_, v_inst_485_, v_inst_486_, v_inst_487_, v_attrKind_boxed_489_);
lean_dec(v_attrInstance_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg(lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_attrInstance_502_){
_start:
{
lean_object* v_toApplicative_503_; lean_object* v_toBind_504_; lean_object* v_toPure_505_; lean_object* v_toMonadRef_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
v_toApplicative_503_ = lean_ctor_get(v_inst_492_, 0);
v_toBind_504_ = lean_ctor_get(v_inst_492_, 1);
v_toPure_505_ = lean_ctor_get(v_toApplicative_503_, 1);
v_toMonadRef_506_ = lean_ctor_get(v_inst_495_, 1);
lean_inc_ref(v_toMonadRef_506_);
v___f_507_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___closed__0));
v___x_508_ = lean_box(0);
v___x_509_ = l_Lean_instInhabitedEffectiveImport_default;
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = l_Lean_Syntax_getArg(v_attrInstance_502_, v___x_510_);
v___x_512_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_512_, 0, v___x_511_);
lean_inc(v_inst_500_);
lean_inc(v_inst_499_);
lean_inc_ref(v_inst_498_);
lean_inc_ref(v_inst_494_);
lean_inc_ref(v_inst_495_);
lean_inc_ref(v_inst_497_);
lean_inc_ref_n(v_inst_493_, 2);
lean_inc_ref(v_inst_496_);
lean_inc_ref_n(v_inst_492_, 2);
v___x_513_ = l_Lean_Elab_liftMacroM___redArg(v_inst_492_, v_inst_496_, v_inst_493_, v_inst_497_, v_inst_495_, v_inst_494_, v_inst_498_, v_inst_499_, v_inst_500_, v___x_512_);
lean_inc_n(v_toBind_504_, 2);
lean_inc(v_toPure_505_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__11___boxed), 18, 17);
lean_closure_set(v___f_514_, 0, v_inst_493_);
lean_closure_set(v___f_514_, 1, v_toPure_505_);
lean_closure_set(v___f_514_, 2, v___x_508_);
lean_closure_set(v___f_514_, 3, v_inst_492_);
lean_closure_set(v___f_514_, 4, v_inst_498_);
lean_closure_set(v___f_514_, 5, v_inst_499_);
lean_closure_set(v___f_514_, 6, v_toMonadRef_506_);
lean_closure_set(v___f_514_, 7, v_inst_500_);
lean_closure_set(v___f_514_, 8, v_toBind_504_);
lean_closure_set(v___f_514_, 9, v___x_509_);
lean_closure_set(v___f_514_, 10, v_inst_495_);
lean_closure_set(v___f_514_, 11, v___x_510_);
lean_closure_set(v___f_514_, 12, v_attrInstance_502_);
lean_closure_set(v___f_514_, 13, v___f_507_);
lean_closure_set(v___f_514_, 14, v_inst_496_);
lean_closure_set(v___f_514_, 15, v_inst_497_);
lean_closure_set(v___f_514_, 16, v_inst_494_);
v___x_515_ = lean_apply_4(v_toBind_504_, lean_box(0), lean_box(0), v___x_513_, v___f_514_);
v___x_516_ = 1;
v___x_517_ = l_Lean_withoutExporting___redArg(v_inst_492_, v_inst_493_, v_inst_501_, v___x_515_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr(lean_object* v_m_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_attrInstance_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_elabAttr___redArg(v_inst_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_inst_523_, v_inst_524_, v_inst_525_, v_inst_526_, v_inst_527_, v_inst_529_, v_attrInstance_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___boxed(lean_object* v_m_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_attrInstance_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Elab_elabAttr(v_m_532_, v_inst_533_, v_inst_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_inst_538_, v_inst_539_, v_inst_540_, v_inst_541_, v_inst_542_, v_inst_543_, v_attrInstance_544_);
lean_dec(v_inst_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0(lean_object* v_toPure_546_, lean_object* v_p_547_){
_start:
{
lean_object* v_snd_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_snd_548_ = lean_ctor_get(v_p_547_, 1);
lean_inc(v_snd_548_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_snd_548_);
v___x_550_ = lean_apply_2(v_toPure_546_, lean_box(0), v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(lean_object* v_toPure_551_, lean_object* v_p_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Elab_elabAttrs___redArg___lam__0(v_toPure_551_, v_p_552_);
lean_dec_ref(v_p_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1(lean_object* v_a_554_, lean_object* v_withRef_555_, lean_object* v___x_556_, lean_object* v_oldRef_557_){
_start:
{
lean_object* v_ref_558_; lean_object* v___x_559_; 
v_ref_558_ = l_Lean_replaceRef(v_a_554_, v_oldRef_557_);
v___x_559_ = lean_apply_3(v_withRef_555_, lean_box(0), v_ref_558_, v___x_556_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(lean_object* v_a_560_, lean_object* v_withRef_561_, lean_object* v___x_562_, lean_object* v_oldRef_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Elab_elabAttrs___redArg___lam__1(v_a_560_, v_withRef_561_, v___x_562_, v_oldRef_563_);
lean_dec(v_oldRef_563_);
lean_dec(v_a_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__2(lean_object* v___y_565_, lean_object* v_toPure_566_, lean_object* v_____do__lift_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_568_ = lean_array_push(v___y_565_, v_____do__lift_567_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
v___x_571_ = lean_apply_2(v_toPure_566_, lean_box(0), v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__3(lean_object* v___y_572_, lean_object* v_toPure_573_, lean_object* v_____r_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_____r_574_);
lean_ctor_set(v___x_575_, 1, v___y_572_);
v___x_576_ = lean_apply_2(v_toPure_573_, lean_box(0), v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__4(lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_toBind_582_, lean_object* v___f_583_, lean_object* v_ex_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = l_Lean_Elab_logException___redArg(v_inst_577_, v_inst_578_, v_inst_579_, v_inst_580_, v_inst_581_, v_ex_584_);
v___x_586_ = lean_apply_4(v_toBind_582_, lean_box(0), lean_box(0), v___x_585_, v___f_583_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5(lean_object* v_toMonadRef_587_, lean_object* v_toMonadExceptOf_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_toBind_599_, lean_object* v_toPure_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v___f_603_, lean_object* v_a_604_, lean_object* v_x_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_getRef_607_; lean_object* v_withRef_608_; lean_object* v_tryCatch_609_; lean_object* v___x_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_getRef_607_ = lean_ctor_get(v_toMonadRef_587_, 0);
lean_inc(v_getRef_607_);
v_withRef_608_ = lean_ctor_get(v_toMonadRef_587_, 1);
lean_inc(v_withRef_608_);
lean_dec_ref(v_toMonadRef_587_);
v_tryCatch_609_ = lean_ctor_get(v_toMonadExceptOf_588_, 1);
lean_inc(v_tryCatch_609_);
lean_dec_ref(v_toMonadExceptOf_588_);
lean_inc(v_a_604_);
lean_inc(v_inst_597_);
lean_inc(v_inst_596_);
lean_inc_ref(v_inst_589_);
v___x_610_ = l_Lean_Elab_elabAttr___redArg(v_inst_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_, v_inst_597_, v_inst_598_, v_a_604_);
v___f_611_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_611_, 0, v_a_604_);
lean_closure_set(v___f_611_, 1, v_withRef_608_);
lean_closure_set(v___f_611_, 2, v___x_610_);
lean_inc_n(v_toBind_599_, 3);
v___x_612_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v_getRef_607_, v___f_611_);
lean_inc(v_toPure_600_);
lean_inc_ref(v___y_606_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__2), 3, 2);
lean_closure_set(v___f_613_, 0, v___y_606_);
lean_closure_set(v___f_613_, 1, v_toPure_600_);
v___f_614_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__3), 3, 2);
lean_closure_set(v___f_614_, 0, v___y_606_);
lean_closure_set(v___f_614_, 1, v_toPure_600_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__4), 8, 7);
lean_closure_set(v___f_615_, 0, v_inst_589_);
lean_closure_set(v___f_615_, 1, v_inst_601_);
lean_closure_set(v___f_615_, 2, v_inst_597_);
lean_closure_set(v___f_615_, 3, v_inst_596_);
lean_closure_set(v___f_615_, 4, v_inst_602_);
lean_closure_set(v___f_615_, 5, v_toBind_599_);
lean_closure_set(v___f_615_, 6, v___f_614_);
v___x_616_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_612_, v___f_613_);
v___x_617_ = lean_apply_3(v_tryCatch_609_, lean_box(0), v___x_616_, v___f_615_);
v___x_618_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_617_, v___f_603_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toMonadRef_619_ = _args[0];
lean_object* v_toMonadExceptOf_620_ = _args[1];
lean_object* v_inst_621_ = _args[2];
lean_object* v_inst_622_ = _args[3];
lean_object* v_inst_623_ = _args[4];
lean_object* v_inst_624_ = _args[5];
lean_object* v_inst_625_ = _args[6];
lean_object* v_inst_626_ = _args[7];
lean_object* v_inst_627_ = _args[8];
lean_object* v_inst_628_ = _args[9];
lean_object* v_inst_629_ = _args[10];
lean_object* v_inst_630_ = _args[11];
lean_object* v_toBind_631_ = _args[12];
lean_object* v_toPure_632_ = _args[13];
lean_object* v_inst_633_ = _args[14];
lean_object* v_inst_634_ = _args[15];
lean_object* v___f_635_ = _args[16];
lean_object* v_a_636_ = _args[17];
lean_object* v_x_637_ = _args[18];
lean_object* v___y_638_ = _args[19];
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Elab_elabAttrs___redArg___lam__5(v_toMonadRef_619_, v_toMonadExceptOf_620_, v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_, v_inst_630_, v_toBind_631_, v_toPure_632_, v_inst_633_, v_inst_634_, v___f_635_, v_a_636_, v_x_637_, v___y_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__6(lean_object* v_toPure_640_, lean_object* v_____s_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_apply_2(v_toPure_640_, lean_box(0), v_____s_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_attrInstances_657_){
_start:
{
lean_object* v_toApplicative_658_; lean_object* v_toBind_659_; lean_object* v_toMonadExceptOf_660_; lean_object* v_toMonadRef_661_; lean_object* v_toPure_662_; lean_object* v_attrs_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___f_666_; size_t v_sz_667_; size_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_toApplicative_658_ = lean_ctor_get(v_inst_645_, 0);
v_toBind_659_ = lean_ctor_get(v_inst_645_, 1);
lean_inc_n(v_toBind_659_, 2);
v_toMonadExceptOf_660_ = lean_ctor_get(v_inst_648_, 0);
lean_inc_ref(v_toMonadExceptOf_660_);
v_toMonadRef_661_ = lean_ctor_get(v_inst_648_, 1);
lean_inc_ref(v_toMonadRef_661_);
v_toPure_662_ = lean_ctor_get(v_toApplicative_658_, 1);
v_attrs_663_ = ((lean_object*)(l_Lean_Elab_elabAttrs___redArg___closed__0));
lean_inc_n(v_toPure_662_, 3);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_664_, 0, v_toPure_662_);
lean_inc_ref(v_inst_645_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__5___boxed), 20, 17);
lean_closure_set(v___f_665_, 0, v_toMonadRef_661_);
lean_closure_set(v___f_665_, 1, v_toMonadExceptOf_660_);
lean_closure_set(v___f_665_, 2, v_inst_645_);
lean_closure_set(v___f_665_, 3, v_inst_646_);
lean_closure_set(v___f_665_, 4, v_inst_647_);
lean_closure_set(v___f_665_, 5, v_inst_648_);
lean_closure_set(v___f_665_, 6, v_inst_649_);
lean_closure_set(v___f_665_, 7, v_inst_650_);
lean_closure_set(v___f_665_, 8, v_inst_651_);
lean_closure_set(v___f_665_, 9, v_inst_652_);
lean_closure_set(v___f_665_, 10, v_inst_653_);
lean_closure_set(v___f_665_, 11, v_inst_656_);
lean_closure_set(v___f_665_, 12, v_toBind_659_);
lean_closure_set(v___f_665_, 13, v_toPure_662_);
lean_closure_set(v___f_665_, 14, v_inst_654_);
lean_closure_set(v___f_665_, 15, v_inst_655_);
lean_closure_set(v___f_665_, 16, v___f_664_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__6), 2, 1);
lean_closure_set(v___f_666_, 0, v_toPure_662_);
v_sz_667_ = lean_array_size(v_attrInstances_657_);
v___x_668_ = ((size_t)0ULL);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_645_, v_attrInstances_657_, v___f_665_, v_sz_667_, v___x_668_, v_attrs_663_);
v___x_670_ = lean_apply_4(v_toBind_659_, lean_box(0), lean_box(0), v___x_669_, v___f_666_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs(lean_object* v_m_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_attrInstances_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Elab_elabAttrs___redArg(v_inst_672_, v_inst_673_, v_inst_674_, v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_inst_679_, v_inst_680_, v_inst_681_, v_inst_682_, v_inst_683_, v_attrInstances_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_stx_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = l_Lean_Syntax_getArg(v_stx_698_, v___x_699_);
v___x_701_ = l_Lean_Syntax_getSepArgs(v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = l_Lean_Elab_elabAttrs___redArg(v_inst_686_, v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_inst_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___boxed(lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_stx_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_703_, v_inst_704_, v_inst_705_, v_inst_706_, v_inst_707_, v_inst_708_, v_inst_709_, v_inst_710_, v_inst_711_, v_inst_712_, v_inst_713_, v_inst_714_, v_stx_715_);
lean_dec(v_stx_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* v_m_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_stx_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_inst_722_, v_inst_723_, v_inst_724_, v_inst_725_, v_inst_726_, v_inst_727_, v_inst_728_, v_inst_729_, v_stx_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___boxed(lean_object* v_m_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_stx_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Elab_elabDeclAttrs(v_m_732_, v_inst_733_, v_inst_734_, v_inst_735_, v_inst_736_, v_inst_737_, v_inst_738_, v_inst_739_, v_inst_740_, v_inst_741_, v_inst_742_, v_inst_743_, v_inst_744_, v_stx_745_);
lean_dec(v_stx_745_);
return v_res_746_;
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
