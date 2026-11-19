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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static const lean_ctor_object l_Lean_Elab_instInhabitedAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__2(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__0));
v___x_11_ = lean_string_length(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__3(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_obj_once(&l_Lean_Elab_instToFormatAttribute___lam__0___closed__2, &l_Lean_Elab_instToFormatAttribute___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__2);
v___x_13_ = lean_nat_to_int(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatAttribute___lam__0(lean_object* v_attr_21_){
_start:
{
uint8_t v_kind_22_; lean_object* v_name_23_; lean_object* v_stx_24_; lean_object* v___y_26_; 
v_kind_22_ = lean_ctor_get_uint8(v_attr_21_, sizeof(void*)*3);
v_name_23_ = lean_ctor_get(v_attr_21_, 0);
lean_inc(v_name_23_);
v_stx_24_ = lean_ctor_get(v_attr_21_, 1);
lean_inc(v_stx_24_);
lean_dec_ref(v_attr_21_);
switch(v_kind_22_)
{
case 0:
{
lean_object* v___x_48_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__6));
v___y_26_ = v___x_48_;
goto v___jp_25_;
}
case 1:
{
lean_object* v___x_49_; 
v___x_49_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__7));
v___y_26_ = v___x_49_;
goto v___jp_25_;
}
default: 
{
lean_object* v___x_50_; 
v___x_50_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__8));
v___y_26_ = v___x_50_;
goto v___jp_25_;
}
}
v___jp_25_:
{
lean_object* v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; 
lean_inc_ref(v___y_26_);
v___x_27_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_27_, 0, v___y_26_);
v___x_28_ = 1;
v___x_29_ = l_Lean_Name_toString(v_name_23_, v___x_28_);
v___x_30_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
v___x_31_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_27_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v___x_32_ = lean_box(0);
v___x_33_ = 0;
v___x_34_ = l_Lean_Syntax_formatStx(v_stx_24_, v___x_32_, v___x_33_);
v___x_35_ = l_Std_Format_defWidth;
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l_Std_Format_pretty(v___x_34_, v___x_35_, v___x_36_, v___x_36_);
v___x_38_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
v___x_39_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_31_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_obj_once(&l_Lean_Elab_instToFormatAttribute___lam__0___closed__3, &l_Lean_Elab_instToFormatAttribute___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__3);
v___x_41_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__4));
v___x_42_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_39_);
v___x_43_ = ((lean_object*)(l_Lean_Elab_instToFormatAttribute___lam__0___closed__5));
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_40_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = 0;
v___x_47_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*1, v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_toAttributeKind(lean_object* v_attrKindStx_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = l_Lean_Syntax_getArg(v_attrKindStx_63_, v___x_66_);
v___x_68_ = l_Lean_Syntax_isNone(v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = l_Lean_Syntax_getArg(v___x_67_, v___x_66_);
lean_dec(v___x_67_);
v___x_70_ = l_Lean_Syntax_getKind(v___x_69_);
v___x_71_ = ((lean_object*)(l_Lean_Elab_toAttributeKind___closed__4));
v___x_72_ = lean_name_eq(v___x_70_, v___x_71_);
lean_dec(v___x_70_);
if (v___x_72_ == 0)
{
uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = 1;
v___x_74_ = lean_box(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v_a_65_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Macro_getCurrNamespace(v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_94_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_a_78_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_94_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_94_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_94_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; 
v___x_82_ = l_Lean_Name_isAnonymous(v_a_77_);
lean_dec(v_a_77_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = 2;
v___x_84_ = lean_box(v___x_83_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_84_);
v___x_86_ = v___x_80_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_a_78_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v_ref_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v_ref_88_ = lean_ctor_get(v_a_64_, 5);
v___x_89_ = ((lean_object*)(l_Lean_Elab_toAttributeKind___closed__5));
lean_inc(v_ref_88_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_ref_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 0, v___x_90_);
v___x_92_ = v___x_80_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_a_78_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_95_ = lean_ctor_get(v___x_76_, 0);
v_a_96_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_76_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_inc(v_a_95_);
lean_dec(v___x_76_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_95_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
else
{
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v___x_67_);
v___x_104_ = 0;
v___x_105_ = lean_box(v___x_104_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_a_65_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object* v_attrKindStx_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_toAttributeKind(v_attrKindStx_107_, v_a_108_, v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_attrKindStx_107_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___redArg___lam__0(lean_object* v_k_141_){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__0___closed__1));
v___x_143_ = lean_name_eq(v_k_141_, v___x_142_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__1(uint8_t v_attrKind_149_, lean_object* v_attrName_150_, lean_object* v_attr_151_, lean_object* v_toPure_152_, lean_object* v_____r_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_155_, 0, v_attrName_150_);
lean_ctor_set(v___x_155_, 1, v_attr_151_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*3, v_attrKind_149_);
v___x_156_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_155_);
return v___x_156_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_toMonadRef_171_, lean_object* v_inst_172_, lean_object* v_ref_173_, uint8_t v___x_174_, lean_object* v_toBind_175_, lean_object* v___f_176_, lean_object* v_____r_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_toMonadRef_171_, v_inst_172_, v_ref_173_, v___x_174_);
v___x_179_ = lean_apply_4(v_toBind_175_, lean_box(0), lean_box(0), v___x_178_, v___f_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__3___boxed(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_toMonadRef_184_, lean_object* v_inst_185_, lean_object* v_ref_186_, lean_object* v___x_187_, lean_object* v_toBind_188_, lean_object* v___f_189_, lean_object* v_____r_190_){
_start:
{
uint8_t v___x_1185__boxed_191_; lean_object* v_res_192_; 
v___x_1185__boxed_191_ = lean_unbox(v___x_187_);
v_res_192_ = l_Lean_Elab_elabAttr___redArg___lam__3(v_inst_180_, v_inst_181_, v_inst_182_, v_inst_183_, v_toMonadRef_184_, v_inst_185_, v_ref_186_, v___x_1185__boxed_191_, v_toBind_188_, v___f_189_, v_____r_190_);
return v_res_192_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__0));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__2));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__4));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__5___closed__6));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5(lean_object* v___f_205_, lean_object* v_val_206_, lean_object* v___x_207_, lean_object* v_attrName_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_toBind_211_, lean_object* v___f_212_, lean_object* v_env_213_){
_start:
{
lean_object* v___x_217_; lean_object* v_modules_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_217_ = l_Lean_Environment_header(v_env_213_);
v_modules_218_ = lean_ctor_get(v___x_217_, 3);
lean_inc_ref(v_modules_218_);
lean_dec_ref(v___x_217_);
v___x_219_ = lean_array_get_size(v_modules_218_);
v___x_220_ = lean_nat_dec_lt(v_val_206_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v_modules_218_);
lean_dec(v___f_212_);
lean_dec(v_toBind_211_);
lean_dec_ref(v_inst_210_);
lean_dec_ref(v_inst_209_);
lean_dec(v_attrName_208_);
goto v___jp_214_;
}
else
{
lean_object* v___x_221_; uint8_t v_hasData_222_; 
v___x_221_ = lean_array_fget_borrowed(v_modules_218_, v_val_206_);
v_hasData_222_ = lean_ctor_get_uint8(v___x_221_, sizeof(void*)*1 + 1);
if (v_hasData_222_ == 0)
{
lean_object* v___x_223_; lean_object* v_toImport_224_; lean_object* v_module_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v___f_205_);
v___x_223_ = lean_array_get(v___x_207_, v_modules_218_, v_val_206_);
lean_dec_ref(v_modules_218_);
v_toImport_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_toImport_224_);
lean_dec(v___x_223_);
v_module_225_ = lean_ctor_get(v_toImport_224_, 0);
lean_inc(v_module_225_);
lean_dec_ref(v_toImport_224_);
v___x_226_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1);
v___x_227_ = l_Lean_MessageData_ofName(v_attrName_208_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_MessageData_ofName(v_module_225_);
lean_inc_ref(v___x_231_);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__5, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_231_);
v___x_236_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__5___closed__7, &l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once, _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7);
v___x_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_throwError___redArg(v_inst_209_, v_inst_210_, v___x_237_);
v___x_239_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_238_, v___f_212_);
return v___x_239_;
}
else
{
lean_dec_ref(v_modules_218_);
lean_dec(v___f_212_);
lean_dec(v_toBind_211_);
lean_dec_ref(v_inst_210_);
lean_dec_ref(v_inst_209_);
lean_dec(v_attrName_208_);
goto v___jp_214_;
}
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_apply_1(v___f_205_, v___x_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__5___boxed(lean_object* v___f_240_, lean_object* v_val_241_, lean_object* v___x_242_, lean_object* v_attrName_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_toBind_246_, lean_object* v___f_247_, lean_object* v_env_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Elab_elabAttr___redArg___lam__5(v___f_240_, v_val_241_, v___x_242_, v_attrName_243_, v_inst_244_, v_inst_245_, v_toBind_246_, v___f_247_, v_env_248_);
lean_dec_ref(v_env_248_);
lean_dec_ref(v___x_242_);
lean_dec(v_val_241_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4(lean_object* v_ref_250_, lean_object* v___f_251_, lean_object* v___x_252_, lean_object* v_attrName_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_toBind_256_, lean_object* v___f_257_, lean_object* v_getEnv_258_, lean_object* v_____do__lift_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_259_, v_ref_250_);
if (lean_obj_tag(v___x_260_) == 1)
{
lean_object* v_val_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v_val_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v___x_260_, 1);
lean_inc(v_toBind_256_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_262_, 0, v___f_251_);
lean_closure_set(v___f_262_, 1, v_val_261_);
lean_closure_set(v___f_262_, 2, v___x_252_);
lean_closure_set(v___f_262_, 3, v_attrName_253_);
lean_closure_set(v___f_262_, 4, v_inst_254_);
lean_closure_set(v___f_262_, 5, v_inst_255_);
lean_closure_set(v___f_262_, 6, v_toBind_256_);
lean_closure_set(v___f_262_, 7, v___f_257_);
v___x_263_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v_getEnv_258_, v___f_262_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v___x_260_);
lean_dec(v_getEnv_258_);
lean_dec(v___f_257_);
lean_dec(v_toBind_256_);
lean_dec_ref(v_inst_255_);
lean_dec_ref(v_inst_254_);
lean_dec(v_attrName_253_);
lean_dec_ref(v___x_252_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v___f_251_, v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__4___boxed(lean_object* v_ref_266_, lean_object* v___f_267_, lean_object* v___x_268_, lean_object* v_attrName_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_toBind_272_, lean_object* v___f_273_, lean_object* v_getEnv_274_, lean_object* v_____do__lift_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_elabAttr___redArg___lam__4(v_ref_266_, v___f_267_, v___x_268_, v_attrName_269_, v_inst_270_, v_inst_271_, v_toBind_272_, v___f_273_, v_getEnv_274_, v_____do__lift_275_);
lean_dec_ref(v_____do__lift_275_);
lean_dec(v_ref_266_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__6(lean_object* v_a_277_, lean_object* v___x_278_, lean_object* v___f_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_toMonadRef_284_, lean_object* v_inst_285_, lean_object* v_toBind_286_, lean_object* v___f_287_, lean_object* v___x_288_, lean_object* v_attrName_289_, lean_object* v_inst_290_, lean_object* v_getEnv_291_, lean_object* v_____do__lift_292_){
_start:
{
lean_object* v_toAttributeImplCore_293_; lean_object* v_ref_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_toAttributeImplCore_293_ = lean_ctor_get(v_a_277_, 0);
lean_inc_ref(v_toAttributeImplCore_293_);
lean_dec_ref(v_a_277_);
v_ref_294_ = lean_ctor_get(v_toAttributeImplCore_293_, 0);
lean_inc_n(v_ref_294_, 2);
lean_dec_ref(v_toAttributeImplCore_293_);
v___x_295_ = l_Lean_regularInitAttr;
v___x_296_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_278_, v___x_295_, v_____do__lift_292_, v_ref_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_ref_294_);
lean_dec(v_getEnv_291_);
lean_dec_ref(v_inst_290_);
lean_dec(v_attrName_289_);
lean_dec_ref(v___x_288_);
lean_dec(v___f_287_);
lean_dec(v_toBind_286_);
lean_dec(v_inst_285_);
lean_dec_ref(v_toMonadRef_284_);
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_apply_1(v___f_279_, v___x_297_);
return v___x_298_;
}
else
{
uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___f_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v___x_296_, 1);
lean_dec(v___f_279_);
v___x_299_ = 1;
v___x_300_ = lean_box(v___x_299_);
lean_inc_n(v_toBind_286_, 2);
lean_inc(v_ref_294_);
lean_inc_ref(v_inst_280_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_301_, 0, v_inst_280_);
lean_closure_set(v___f_301_, 1, v_inst_281_);
lean_closure_set(v___f_301_, 2, v_inst_282_);
lean_closure_set(v___f_301_, 3, v_inst_283_);
lean_closure_set(v___f_301_, 4, v_toMonadRef_284_);
lean_closure_set(v___f_301_, 5, v_inst_285_);
lean_closure_set(v___f_301_, 6, v_ref_294_);
lean_closure_set(v___f_301_, 7, v___x_300_);
lean_closure_set(v___f_301_, 8, v_toBind_286_);
lean_closure_set(v___f_301_, 9, v___f_287_);
lean_inc_ref(v___f_301_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_302_, 0, v___f_301_);
lean_inc(v_getEnv_291_);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_303_, 0, v_ref_294_);
lean_closure_set(v___f_303_, 1, v___f_301_);
lean_closure_set(v___f_303_, 2, v___x_288_);
lean_closure_set(v___f_303_, 3, v_attrName_289_);
lean_closure_set(v___f_303_, 4, v_inst_280_);
lean_closure_set(v___f_303_, 5, v_inst_290_);
lean_closure_set(v___f_303_, 6, v_toBind_286_);
lean_closure_set(v___f_303_, 7, v___f_302_);
lean_closure_set(v___f_303_, 8, v_getEnv_291_);
v___x_304_ = lean_apply_4(v_toBind_286_, lean_box(0), lean_box(0), v_getEnv_291_, v___f_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__7(lean_object* v_attrName_305_, lean_object* v___x_306_, lean_object* v___f_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_toMonadRef_312_, lean_object* v_inst_313_, lean_object* v_toBind_314_, lean_object* v___f_315_, lean_object* v___x_316_, lean_object* v_inst_317_, lean_object* v_getEnv_318_, lean_object* v_____do__lift_319_){
_start:
{
lean_object* v___x_320_; 
lean_inc(v_attrName_305_);
v___x_320_ = l_Lean_getAttributeImpl(v_____do__lift_319_, v_attrName_305_);
if (lean_obj_tag(v___x_320_) == 1)
{
lean_object* v_a_321_; lean_object* v___f_322_; lean_object* v___x_323_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
lean_inc(v_getEnv_318_);
lean_inc(v_toBind_314_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__6), 16, 15);
lean_closure_set(v___f_322_, 0, v_a_321_);
lean_closure_set(v___f_322_, 1, v___x_306_);
lean_closure_set(v___f_322_, 2, v___f_307_);
lean_closure_set(v___f_322_, 3, v_inst_308_);
lean_closure_set(v___f_322_, 4, v_inst_309_);
lean_closure_set(v___f_322_, 5, v_inst_310_);
lean_closure_set(v___f_322_, 6, v_inst_311_);
lean_closure_set(v___f_322_, 7, v_toMonadRef_312_);
lean_closure_set(v___f_322_, 8, v_inst_313_);
lean_closure_set(v___f_322_, 9, v_toBind_314_);
lean_closure_set(v___f_322_, 10, v___f_315_);
lean_closure_set(v___f_322_, 11, v___x_316_);
lean_closure_set(v___f_322_, 12, v_attrName_305_);
lean_closure_set(v___f_322_, 13, v_inst_317_);
lean_closure_set(v___f_322_, 14, v_getEnv_318_);
v___x_323_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v_getEnv_318_, v___f_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref(v___x_320_);
lean_dec(v_getEnv_318_);
lean_dec_ref(v_inst_317_);
lean_dec_ref(v___x_316_);
lean_dec(v___f_315_);
lean_dec(v_toBind_314_);
lean_dec(v_inst_313_);
lean_dec_ref(v_toMonadRef_312_);
lean_dec_ref(v_inst_311_);
lean_dec_ref(v_inst_310_);
lean_dec_ref(v_inst_309_);
lean_dec_ref(v_inst_308_);
lean_dec(v___x_306_);
lean_dec(v_attrName_305_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_apply_1(v___f_307_, v___x_324_);
return v___x_325_;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__0));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__8___closed__2));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__8(lean_object* v_attrName_332_, lean_object* v_toBind_333_, lean_object* v_getEnv_334_, lean_object* v___f_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_____do__lift_338_){
_start:
{
lean_object* v___x_339_; 
lean_inc(v_attrName_332_);
v___x_339_ = l_Lean_getAttributeImpl(v_____do__lift_338_, v_attrName_332_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v___x_340_; 
lean_dec_ref_known(v___x_339_, 1);
lean_dec_ref(v_inst_337_);
lean_dec_ref(v_inst_336_);
lean_dec(v_attrName_332_);
v___x_340_ = lean_apply_4(v_toBind_333_, lean_box(0), lean_box(0), v_getEnv_334_, v___f_335_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v___x_339_);
lean_dec(v___f_335_);
lean_dec(v_getEnv_334_);
lean_dec(v_toBind_333_);
v___x_341_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__1, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1);
v___x_342_ = l_Lean_MessageData_ofName(v_attrName_332_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__8___closed__3, &l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once, _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwError___redArg(v_inst_336_, v_inst_337_, v___x_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9(lean_object* v_inst_347_, uint8_t v_attrKind_348_, lean_object* v_attr_349_, lean_object* v_toPure_350_, lean_object* v___x_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_toMonadRef_355_, lean_object* v_inst_356_, lean_object* v_toBind_357_, lean_object* v___x_358_, lean_object* v_inst_359_, lean_object* v_attrName_360_){
_start:
{
lean_object* v_getEnv_361_; lean_object* v___x_362_; lean_object* v___f_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___x_367_; 
v_getEnv_361_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_n(v_getEnv_361_, 3);
v___x_362_ = lean_box(v_attrKind_348_);
lean_inc_n(v_attrName_360_, 2);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_363_, 0, v___x_362_);
lean_closure_set(v___f_363_, 1, v_attrName_360_);
lean_closure_set(v___f_363_, 2, v_attr_349_);
lean_closure_set(v___f_363_, 3, v_toPure_350_);
lean_inc_ref(v___f_363_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__2), 2, 1);
lean_closure_set(v___f_364_, 0, v___f_363_);
lean_inc_ref(v_inst_359_);
lean_inc_n(v_toBind_357_, 2);
lean_inc_ref(v_inst_352_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__7), 15, 14);
lean_closure_set(v___f_365_, 0, v_attrName_360_);
lean_closure_set(v___f_365_, 1, v___x_351_);
lean_closure_set(v___f_365_, 2, v___f_363_);
lean_closure_set(v___f_365_, 3, v_inst_352_);
lean_closure_set(v___f_365_, 4, v_inst_347_);
lean_closure_set(v___f_365_, 5, v_inst_353_);
lean_closure_set(v___f_365_, 6, v_inst_354_);
lean_closure_set(v___f_365_, 7, v_toMonadRef_355_);
lean_closure_set(v___f_365_, 8, v_inst_356_);
lean_closure_set(v___f_365_, 9, v_toBind_357_);
lean_closure_set(v___f_365_, 10, v___f_364_);
lean_closure_set(v___f_365_, 11, v___x_358_);
lean_closure_set(v___f_365_, 12, v_inst_359_);
lean_closure_set(v___f_365_, 13, v_getEnv_361_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__8), 7, 6);
lean_closure_set(v___f_366_, 0, v_attrName_360_);
lean_closure_set(v___f_366_, 1, v_toBind_357_);
lean_closure_set(v___f_366_, 2, v_getEnv_361_);
lean_closure_set(v___f_366_, 3, v___f_365_);
lean_closure_set(v___f_366_, 4, v_inst_352_);
lean_closure_set(v___f_366_, 5, v_inst_359_);
v___x_367_ = lean_apply_4(v_toBind_357_, lean_box(0), lean_box(0), v_getEnv_361_, v___f_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__9___boxed(lean_object* v_inst_368_, lean_object* v_attrKind_369_, lean_object* v_attr_370_, lean_object* v_toPure_371_, lean_object* v___x_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_toMonadRef_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v___x_379_, lean_object* v_inst_380_, lean_object* v_attrName_381_){
_start:
{
uint8_t v_attrKind_boxed_382_; lean_object* v_res_383_; 
v_attrKind_boxed_382_ = lean_unbox(v_attrKind_369_);
v_res_383_ = l_Lean_Elab_elabAttr___redArg___lam__9(v_inst_368_, v_attrKind_boxed_382_, v_attr_370_, v_toPure_371_, v___x_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_toMonadRef_376_, v_inst_377_, v_toBind_378_, v___x_379_, v_inst_380_, v_attrName_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__10(lean_object* v___f_384_, lean_object* v_attrName_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_apply_1(v___f_384_, v_attrName_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__3));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13(lean_object* v_inst_397_, uint8_t v_attrKind_398_, lean_object* v_toPure_399_, lean_object* v___x_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_toMonadRef_404_, lean_object* v_inst_405_, lean_object* v_toBind_406_, lean_object* v___x_407_, lean_object* v_inst_408_, lean_object* v___x_409_, lean_object* v_attr_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_411_ = lean_box(v_attrKind_398_);
lean_inc_ref(v_inst_408_);
lean_inc(v_toBind_406_);
lean_inc_ref(v_inst_401_);
lean_inc(v_toPure_399_);
lean_inc_n(v_attr_410_, 2);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_412_, 0, v_inst_397_);
lean_closure_set(v___f_412_, 1, v___x_411_);
lean_closure_set(v___f_412_, 2, v_attr_410_);
lean_closure_set(v___f_412_, 3, v_toPure_399_);
lean_closure_set(v___f_412_, 4, v___x_400_);
lean_closure_set(v___f_412_, 5, v_inst_401_);
lean_closure_set(v___f_412_, 6, v_inst_402_);
lean_closure_set(v___f_412_, 7, v_inst_403_);
lean_closure_set(v___f_412_, 8, v_toMonadRef_404_);
lean_closure_set(v___f_412_, 9, v_inst_405_);
lean_closure_set(v___f_412_, 10, v_toBind_406_);
lean_closure_set(v___f_412_, 11, v___x_407_);
lean_closure_set(v___f_412_, 12, v_inst_408_);
v___x_413_ = l_Lean_Syntax_getKind(v_attr_410_);
v___x_414_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2));
v___x_415_ = lean_name_eq(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
if (lean_obj_tag(v___x_413_) == 1)
{
lean_object* v_str_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_attr_410_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_401_);
v_str_416_ = lean_ctor_get(v___x_413_, 1);
lean_inc_ref(v_str_416_);
lean_dec_ref_known(v___x_413_, 2);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_417_, 0, v___f_412_);
v___x_418_ = lean_box(0);
v___x_419_ = l_Lean_Name_str___override(v___x_418_, v_str_416_);
v___x_420_ = lean_apply_2(v_toPure_399_, lean_box(0), v___x_419_);
v___x_421_ = lean_apply_4(v_toBind_406_, lean_box(0), lean_box(0), v___x_420_, v___f_417_);
return v___x_421_;
}
else
{
lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_413_);
lean_dec(v_toPure_399_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_422_, 0, v___f_412_);
v___x_423_ = lean_obj_once(&l_Lean_Elab_elabAttr___redArg___lam__13___closed__4, &l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once, _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4);
v___x_424_ = l_Lean_throwErrorAt___redArg(v_inst_401_, v_inst_408_, v_attr_410_, v___x_423_);
v___x_425_ = lean_apply_4(v_toBind_406_, lean_box(0), lean_box(0), v___x_424_, v___f_422_);
return v___x_425_;
}
}
else
{
lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v___x_413_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_401_);
v___f_426_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__10), 2, 1);
lean_closure_set(v___f_426_, 0, v___f_412_);
v___x_427_ = l_Lean_Syntax_getArg(v_attr_410_, v___x_409_);
lean_dec(v_attr_410_);
v___x_428_ = l_Lean_Syntax_getId(v___x_427_);
lean_dec(v___x_427_);
v___x_429_ = l_Lean_Name_eraseMacroScopes(v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = lean_apply_2(v_toPure_399_, lean_box(0), v___x_429_);
v___x_431_ = lean_apply_4(v_toBind_406_, lean_box(0), lean_box(0), v___x_430_, v___f_426_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__13___boxed(lean_object* v_inst_432_, lean_object* v_attrKind_433_, lean_object* v_toPure_434_, lean_object* v___x_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_toMonadRef_439_, lean_object* v_inst_440_, lean_object* v_toBind_441_, lean_object* v___x_442_, lean_object* v_inst_443_, lean_object* v___x_444_, lean_object* v_attr_445_){
_start:
{
uint8_t v_attrKind_boxed_446_; lean_object* v_res_447_; 
v_attrKind_boxed_446_ = lean_unbox(v_attrKind_433_);
v_res_447_ = l_Lean_Elab_elabAttr___redArg___lam__13(v_inst_432_, v_attrKind_boxed_446_, v_toPure_434_, v___x_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_toMonadRef_439_, v_inst_440_, v_toBind_441_, v___x_442_, v_inst_443_, v___x_444_, v_attr_445_);
lean_dec(v___x_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11(lean_object* v_inst_448_, lean_object* v_toPure_449_, lean_object* v___x_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_toMonadRef_454_, lean_object* v_inst_455_, lean_object* v_toBind_456_, lean_object* v___x_457_, lean_object* v_inst_458_, lean_object* v___x_459_, lean_object* v_attrInstance_460_, lean_object* v___f_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, uint8_t v_attrKind_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v_attr_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_466_ = lean_box(v_attrKind_465_);
lean_inc_ref(v_inst_458_);
lean_inc(v_toBind_456_);
lean_inc(v_inst_455_);
lean_inc_ref(v_inst_453_);
lean_inc_ref(v_inst_452_);
lean_inc_ref(v_inst_451_);
lean_inc_ref(v_inst_448_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__13___boxed), 14, 13);
lean_closure_set(v___f_467_, 0, v_inst_448_);
lean_closure_set(v___f_467_, 1, v___x_466_);
lean_closure_set(v___f_467_, 2, v_toPure_449_);
lean_closure_set(v___f_467_, 3, v___x_450_);
lean_closure_set(v___f_467_, 4, v_inst_451_);
lean_closure_set(v___f_467_, 5, v_inst_452_);
lean_closure_set(v___f_467_, 6, v_inst_453_);
lean_closure_set(v___f_467_, 7, v_toMonadRef_454_);
lean_closure_set(v___f_467_, 8, v_inst_455_);
lean_closure_set(v___f_467_, 9, v_toBind_456_);
lean_closure_set(v___f_467_, 10, v___x_457_);
lean_closure_set(v___f_467_, 11, v_inst_458_);
lean_closure_set(v___f_467_, 12, v___x_459_);
v___x_468_ = lean_unsigned_to_nat(1u);
v_attr_469_ = l_Lean_Syntax_getArg(v_attrInstance_460_, v___x_468_);
v___x_470_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_470_, 0, v_attr_469_);
lean_closure_set(v___x_470_, 1, v___f_461_);
v___x_471_ = l_Lean_Elab_liftMacroM___redArg(v_inst_451_, v_inst_462_, v_inst_448_, v_inst_463_, v_inst_458_, v_inst_464_, v_inst_452_, v_inst_453_, v_inst_455_, v___x_470_);
v___x_472_ = lean_apply_4(v_toBind_456_, lean_box(0), lean_box(0), v___x_471_, v___f_467_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_473_ = _args[0];
lean_object* v_toPure_474_ = _args[1];
lean_object* v___x_475_ = _args[2];
lean_object* v_inst_476_ = _args[3];
lean_object* v_inst_477_ = _args[4];
lean_object* v_inst_478_ = _args[5];
lean_object* v_toMonadRef_479_ = _args[6];
lean_object* v_inst_480_ = _args[7];
lean_object* v_toBind_481_ = _args[8];
lean_object* v___x_482_ = _args[9];
lean_object* v_inst_483_ = _args[10];
lean_object* v___x_484_ = _args[11];
lean_object* v_attrInstance_485_ = _args[12];
lean_object* v___f_486_ = _args[13];
lean_object* v_inst_487_ = _args[14];
lean_object* v_inst_488_ = _args[15];
lean_object* v_inst_489_ = _args[16];
lean_object* v_attrKind_490_ = _args[17];
_start:
{
uint8_t v_attrKind_boxed_491_; lean_object* v_res_492_; 
v_attrKind_boxed_491_ = lean_unbox(v_attrKind_490_);
v_res_492_ = l_Lean_Elab_elabAttr___redArg___lam__11(v_inst_473_, v_toPure_474_, v___x_475_, v_inst_476_, v_inst_477_, v_inst_478_, v_toMonadRef_479_, v_inst_480_, v_toBind_481_, v___x_482_, v_inst_483_, v___x_484_, v_attrInstance_485_, v___f_486_, v_inst_487_, v_inst_488_, v_inst_489_, v_attrKind_boxed_491_);
lean_dec(v_attrInstance_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___redArg(lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_attrInstance_504_){
_start:
{
lean_object* v_toApplicative_505_; lean_object* v_toBind_506_; lean_object* v_toPure_507_; lean_object* v_toMonadRef_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___f_516_; lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; 
v_toApplicative_505_ = lean_ctor_get(v_inst_494_, 0);
v_toBind_506_ = lean_ctor_get(v_inst_494_, 1);
v_toPure_507_ = lean_ctor_get(v_toApplicative_505_, 1);
v_toMonadRef_508_ = lean_ctor_get(v_inst_497_, 1);
lean_inc_ref(v_toMonadRef_508_);
v___f_509_ = ((lean_object*)(l_Lean_Elab_elabAttr___redArg___closed__0));
v___x_510_ = lean_box(0);
v___x_511_ = l_Lean_instInhabitedEffectiveImport_default;
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_Syntax_getArg(v_attrInstance_504_, v___x_512_);
v___x_514_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_514_, 0, v___x_513_);
lean_inc(v_inst_502_);
lean_inc_ref(v_inst_501_);
lean_inc_ref(v_inst_500_);
lean_inc_ref(v_inst_496_);
lean_inc_ref(v_inst_497_);
lean_inc_ref(v_inst_499_);
lean_inc_ref_n(v_inst_495_, 2);
lean_inc_ref(v_inst_498_);
lean_inc_ref_n(v_inst_494_, 2);
v___x_515_ = l_Lean_Elab_liftMacroM___redArg(v_inst_494_, v_inst_498_, v_inst_495_, v_inst_499_, v_inst_497_, v_inst_496_, v_inst_500_, v_inst_501_, v_inst_502_, v___x_514_);
lean_inc_n(v_toBind_506_, 2);
lean_inc(v_toPure_507_);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___redArg___lam__11___boxed), 18, 17);
lean_closure_set(v___f_516_, 0, v_inst_495_);
lean_closure_set(v___f_516_, 1, v_toPure_507_);
lean_closure_set(v___f_516_, 2, v___x_510_);
lean_closure_set(v___f_516_, 3, v_inst_494_);
lean_closure_set(v___f_516_, 4, v_inst_500_);
lean_closure_set(v___f_516_, 5, v_inst_501_);
lean_closure_set(v___f_516_, 6, v_toMonadRef_508_);
lean_closure_set(v___f_516_, 7, v_inst_502_);
lean_closure_set(v___f_516_, 8, v_toBind_506_);
lean_closure_set(v___f_516_, 9, v___x_511_);
lean_closure_set(v___f_516_, 10, v_inst_497_);
lean_closure_set(v___f_516_, 11, v___x_512_);
lean_closure_set(v___f_516_, 12, v_attrInstance_504_);
lean_closure_set(v___f_516_, 13, v___f_509_);
lean_closure_set(v___f_516_, 14, v_inst_498_);
lean_closure_set(v___f_516_, 15, v_inst_499_);
lean_closure_set(v___f_516_, 16, v_inst_496_);
v___x_517_ = lean_apply_4(v_toBind_506_, lean_box(0), lean_box(0), v___x_515_, v___f_516_);
v___x_518_ = 1;
v___x_519_ = l_Lean_withoutExporting___redArg(v_inst_494_, v_inst_495_, v_inst_503_, v___x_517_, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr(lean_object* v_m_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_attrInstance_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Elab_elabAttr___redArg(v_inst_521_, v_inst_522_, v_inst_523_, v_inst_524_, v_inst_525_, v_inst_526_, v_inst_527_, v_inst_528_, v_inst_529_, v_inst_531_, v_attrInstance_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___boxed(lean_object* v_m_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_attrInstance_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_elabAttr(v_m_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_inst_538_, v_inst_539_, v_inst_540_, v_inst_541_, v_inst_542_, v_inst_543_, v_inst_544_, v_inst_545_, v_attrInstance_546_);
lean_dec(v_inst_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0(lean_object* v_toPure_548_, lean_object* v_p_549_){
_start:
{
lean_object* v_snd_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_snd_550_ = lean_ctor_get(v_p_549_, 1);
lean_inc(v_snd_550_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_snd_550_);
v___x_552_ = lean_apply_2(v_toPure_548_, lean_box(0), v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(lean_object* v_toPure_553_, lean_object* v_p_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_elabAttrs___redArg___lam__0(v_toPure_553_, v_p_554_);
lean_dec_ref(v_p_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1(lean_object* v_a_556_, lean_object* v_withRef_557_, lean_object* v___x_558_, lean_object* v_oldRef_559_){
_start:
{
lean_object* v_ref_560_; lean_object* v___x_561_; 
v_ref_560_ = l_Lean_replaceRef(v_a_556_, v_oldRef_559_);
v___x_561_ = lean_apply_3(v_withRef_557_, lean_box(0), v_ref_560_, v___x_558_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(lean_object* v_a_562_, lean_object* v_withRef_563_, lean_object* v___x_564_, lean_object* v_oldRef_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Elab_elabAttrs___redArg___lam__1(v_a_562_, v_withRef_563_, v___x_564_, v_oldRef_565_);
lean_dec(v_oldRef_565_);
lean_dec(v_a_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__2(lean_object* v___y_567_, lean_object* v_toPure_568_, lean_object* v_____do__lift_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_array_push(v___y_567_, v_____do__lift_569_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
v___x_573_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__3(lean_object* v___y_574_, lean_object* v_toPure_575_, lean_object* v_____r_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_____r_576_);
lean_ctor_set(v___x_577_, 1, v___y_574_);
v___x_578_ = lean_apply_2(v_toPure_575_, lean_box(0), v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__4(lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_toBind_584_, lean_object* v___f_585_, lean_object* v_ex_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Elab_logException___redArg(v_inst_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_ex_586_);
v___x_588_ = lean_apply_4(v_toBind_584_, lean_box(0), lean_box(0), v___x_587_, v___f_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5(lean_object* v_toMonadRef_589_, lean_object* v_toMonadExceptOf_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_toBind_601_, lean_object* v_toPure_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v___f_605_, lean_object* v_a_606_, lean_object* v_x_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_getRef_609_; lean_object* v_withRef_610_; lean_object* v_tryCatch_611_; lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_getRef_609_ = lean_ctor_get(v_toMonadRef_589_, 0);
lean_inc(v_getRef_609_);
v_withRef_610_ = lean_ctor_get(v_toMonadRef_589_, 1);
lean_inc(v_withRef_610_);
lean_dec_ref(v_toMonadRef_589_);
v_tryCatch_611_ = lean_ctor_get(v_toMonadExceptOf_590_, 1);
lean_inc(v_tryCatch_611_);
lean_dec_ref(v_toMonadExceptOf_590_);
lean_inc(v_a_606_);
lean_inc(v_inst_599_);
lean_inc_ref(v_inst_598_);
lean_inc_ref(v_inst_591_);
v___x_612_ = l_Lean_Elab_elabAttr___redArg(v_inst_591_, v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_, v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_a_606_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_613_, 0, v_a_606_);
lean_closure_set(v___f_613_, 1, v_withRef_610_);
lean_closure_set(v___f_613_, 2, v___x_612_);
lean_inc_n(v_toBind_601_, 3);
v___x_614_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v_getRef_609_, v___f_613_);
lean_inc(v_toPure_602_);
lean_inc_ref(v___y_608_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__2), 3, 2);
lean_closure_set(v___f_615_, 0, v___y_608_);
lean_closure_set(v___f_615_, 1, v_toPure_602_);
v___f_616_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__3), 3, 2);
lean_closure_set(v___f_616_, 0, v___y_608_);
lean_closure_set(v___f_616_, 1, v_toPure_602_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__4), 8, 7);
lean_closure_set(v___f_617_, 0, v_inst_591_);
lean_closure_set(v___f_617_, 1, v_inst_603_);
lean_closure_set(v___f_617_, 2, v_inst_599_);
lean_closure_set(v___f_617_, 3, v_inst_598_);
lean_closure_set(v___f_617_, 4, v_inst_604_);
lean_closure_set(v___f_617_, 5, v_toBind_601_);
lean_closure_set(v___f_617_, 6, v___f_616_);
v___x_618_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_614_, v___f_615_);
v___x_619_ = lean_apply_3(v_tryCatch_611_, lean_box(0), v___x_618_, v___f_617_);
v___x_620_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_619_, v___f_605_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toMonadRef_621_ = _args[0];
lean_object* v_toMonadExceptOf_622_ = _args[1];
lean_object* v_inst_623_ = _args[2];
lean_object* v_inst_624_ = _args[3];
lean_object* v_inst_625_ = _args[4];
lean_object* v_inst_626_ = _args[5];
lean_object* v_inst_627_ = _args[6];
lean_object* v_inst_628_ = _args[7];
lean_object* v_inst_629_ = _args[8];
lean_object* v_inst_630_ = _args[9];
lean_object* v_inst_631_ = _args[10];
lean_object* v_inst_632_ = _args[11];
lean_object* v_toBind_633_ = _args[12];
lean_object* v_toPure_634_ = _args[13];
lean_object* v_inst_635_ = _args[14];
lean_object* v_inst_636_ = _args[15];
lean_object* v___f_637_ = _args[16];
lean_object* v_a_638_ = _args[17];
lean_object* v_x_639_ = _args[18];
lean_object* v___y_640_ = _args[19];
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Elab_elabAttrs___redArg___lam__5(v_toMonadRef_621_, v_toMonadExceptOf_622_, v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_toBind_633_, v_toPure_634_, v_inst_635_, v_inst_636_, v___f_637_, v_a_638_, v_x_639_, v___y_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg___lam__6(lean_object* v_toPure_642_, lean_object* v_____s_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_apply_2(v_toPure_642_, lean_box(0), v_____s_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___redArg(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_attrInstances_659_){
_start:
{
lean_object* v_toApplicative_660_; lean_object* v_toBind_661_; lean_object* v_toMonadExceptOf_662_; lean_object* v_toMonadRef_663_; lean_object* v_toPure_664_; lean_object* v_attrs_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___f_668_; size_t v_sz_669_; size_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_toApplicative_660_ = lean_ctor_get(v_inst_647_, 0);
v_toBind_661_ = lean_ctor_get(v_inst_647_, 1);
lean_inc_n(v_toBind_661_, 2);
v_toMonadExceptOf_662_ = lean_ctor_get(v_inst_650_, 0);
lean_inc_ref(v_toMonadExceptOf_662_);
v_toMonadRef_663_ = lean_ctor_get(v_inst_650_, 1);
lean_inc_ref(v_toMonadRef_663_);
v_toPure_664_ = lean_ctor_get(v_toApplicative_660_, 1);
v_attrs_665_ = ((lean_object*)(l_Lean_Elab_elabAttrs___redArg___closed__0));
lean_inc_n(v_toPure_664_, 3);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_666_, 0, v_toPure_664_);
lean_inc_ref(v_inst_647_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__5___boxed), 20, 17);
lean_closure_set(v___f_667_, 0, v_toMonadRef_663_);
lean_closure_set(v___f_667_, 1, v_toMonadExceptOf_662_);
lean_closure_set(v___f_667_, 2, v_inst_647_);
lean_closure_set(v___f_667_, 3, v_inst_648_);
lean_closure_set(v___f_667_, 4, v_inst_649_);
lean_closure_set(v___f_667_, 5, v_inst_650_);
lean_closure_set(v___f_667_, 6, v_inst_651_);
lean_closure_set(v___f_667_, 7, v_inst_652_);
lean_closure_set(v___f_667_, 8, v_inst_653_);
lean_closure_set(v___f_667_, 9, v_inst_654_);
lean_closure_set(v___f_667_, 10, v_inst_655_);
lean_closure_set(v___f_667_, 11, v_inst_658_);
lean_closure_set(v___f_667_, 12, v_toBind_661_);
lean_closure_set(v___f_667_, 13, v_toPure_664_);
lean_closure_set(v___f_667_, 14, v_inst_656_);
lean_closure_set(v___f_667_, 15, v_inst_657_);
lean_closure_set(v___f_667_, 16, v___f_666_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___redArg___lam__6), 2, 1);
lean_closure_set(v___f_668_, 0, v_toPure_664_);
v_sz_669_ = lean_array_size(v_attrInstances_659_);
v___x_670_ = ((size_t)0ULL);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_647_, v_attrInstances_659_, v___f_667_, v_sz_669_, v___x_670_, v_attrs_665_);
v___x_672_ = lean_apply_4(v_toBind_661_, lean_box(0), lean_box(0), v___x_671_, v___f_668_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs(lean_object* v_m_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_attrInstances_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Elab_elabAttrs___redArg(v_inst_674_, v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_inst_679_, v_inst_680_, v_inst_681_, v_inst_682_, v_inst_683_, v_inst_684_, v_inst_685_, v_attrInstances_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__0(lean_object* v_stx_688_, lean_object* v_x_689_){
_start:
{
uint8_t v_kind_690_; lean_object* v_name_691_; lean_object* v_stx_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_kind_690_ = lean_ctor_get_uint8(v_x_689_, sizeof(void*)*3);
v_name_691_ = lean_ctor_get(v_x_689_, 0);
v_stx_692_ = lean_ctor_get(v_x_689_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_x_689_, 2);
lean_dec(v_unused_701_);
v___x_694_ = v_x_689_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_stx_692_);
lean_inc(v_name_691_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_stx_688_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 2, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_name_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_stx_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v___x_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_699_, sizeof(void*)*3, v_kind_690_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg___lam__1(lean_object* v___f_721_, lean_object* v_toPure_722_, lean_object* v_____do__lift_723_){
_start:
{
lean_object* v___x_724_; size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_724_ = ((lean_object*)(l_Lean_Elab_elabDeclAttrs___redArg___lam__1___closed__9));
v_sz_725_ = lean_array_size(v_____do__lift_723_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_724_, v___f_721_, v_sz_725_, v___x_726_, v_____do__lift_723_);
v___x_728_ = lean_apply_2(v_toPure_722_, lean_box(0), v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_stx_741_){
_start:
{
lean_object* v_toApplicative_742_; lean_object* v_toBind_743_; lean_object* v_toPure_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___x_751_; 
v_toApplicative_742_ = lean_ctor_get(v_inst_729_, 0);
v_toBind_743_ = lean_ctor_get(v_inst_729_, 1);
lean_inc(v_toBind_743_);
v_toPure_744_ = lean_ctor_get(v_toApplicative_742_, 1);
lean_inc(v_toPure_744_);
lean_inc(v_stx_741_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Elab_elabDeclAttrs___redArg___lam__0), 2, 1);
lean_closure_set(v___f_745_, 0, v_stx_741_);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = l_Lean_Syntax_getArg(v_stx_741_, v___x_746_);
lean_dec(v_stx_741_);
v___x_748_ = l_Lean_Syntax_getSepArgs(v___x_747_);
lean_dec(v___x_747_);
v___x_749_ = l_Lean_Elab_elabAttrs___redArg(v_inst_729_, v_inst_730_, v_inst_731_, v_inst_732_, v_inst_733_, v_inst_734_, v_inst_735_, v_inst_736_, v_inst_737_, v_inst_738_, v_inst_739_, v_inst_740_, v___x_748_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Elab_elabDeclAttrs___redArg___lam__1), 3, 2);
lean_closure_set(v___f_750_, 0, v___f_745_);
lean_closure_set(v___f_750_, 1, v_toPure_744_);
v___x_751_ = lean_apply_4(v_toBind_743_, lean_box(0), lean_box(0), v___x_749_, v___f_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* v_m_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_stx_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_753_, v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v_inst_758_, v_inst_759_, v_inst_760_, v_inst_761_, v_inst_762_, v_inst_763_, v_inst_764_, v_stx_765_);
return v___x_766_;
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
