// Lean compiler output
// Module: Lean.Widget.Commands
// Imports: public meta import Lean.Widget.UserWidget public import Init.Notation import Lean.Attributes
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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "widgetInstanceSpec"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__0 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__0_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__1 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Widget"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__2 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_1),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 43, 105, 195, 200, 35, 64, 193)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__3 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__3_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__4 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__4_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__5 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__6 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__6_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__7 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__7_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__7_value)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__8 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__8_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__9 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__9_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__9_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__10 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__10_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "with "};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__11 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__11_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__11_value)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__12 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__12_value;
static const lean_string_object l_Lean_Widget_widgetInstanceSpec___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__13 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__13_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__14 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__14_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__15 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__15_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__12_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__15_value)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__16 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__16_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__10_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__16_value)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__17 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__17_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__8_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__17_value)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__18 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__18_value;
static const lean_ctor_object l_Lean_Widget_widgetInstanceSpec___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__0_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__3_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__18_value)}};
static const lean_object* l_Lean_Widget_widgetInstanceSpec___closed__19 = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__19_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_widgetInstanceSpec = (const lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__19_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "javascriptHash"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(60, 110, 51, 206, 110, 51, 190, 4)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40_value),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44_value)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37_value),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45_value)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ToModule.toModule"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToModule"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toModule"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value),LEAN_SCALAR_PTR_LITERAL(253, 179, 245, 63, 235, 253, 66, 181)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value),LEAN_SCALAR_PTR_LITERAL(150, 248, 26, 83, 63, 136, 226, 191)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value),LEAN_SCALAR_PTR_LITERAL(128, 245, 164, 144, 51, 121, 0, 192)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value),LEAN_SCALAR_PTR_LITERAL(127, 158, 235, 43, 214, 142, 113, 225)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "props"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59_value),LEAN_SCALAR_PTR_LITERAL(81, 109, 51, 84, 90, 92, 70, 19)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Server.RpcEncodable.rpcEncode"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RpcEncodable"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcEncode"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value),LEAN_SCALAR_PTR_LITERAL(154, 127, 234, 255, 208, 218, 159, 21)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(40, 69, 103, 196, 247, 23, 35, 197)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value),LEAN_SCALAR_PTR_LITERAL(26, 58, 71, 199, 118, 20, 218, 18)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value),LEAN_SCALAR_PTR_LITERAL(147, 95, 3, 206, 143, 66, 59, 169)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "WidgetInstance"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74_value),LEAN_SCALAR_PTR_LITERAL(18, 26, 248, 187, 7, 143, 98, 88)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76;
static lean_once_cell_t l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78_value;
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_2),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value;
static const lean_string_object l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80 = (const lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_elabWidgetInstanceSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Json.mkObj"};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__0 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__0_value;
static lean_once_cell_t l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__1;
static const lean_string_object l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Json"};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__2 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value;
static const lean_string_object l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkObj"};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__3 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value;
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value_aux_0),((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 196, 116, 61, 5, 129, 122, 6)}};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__4 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value;
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_0),((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_1),((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(249, 119, 229, 103, 93, 90, 238, 17)}};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__5 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value;
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__6 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__6_value;
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__7 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__7_value;
static const lean_string_object l_Lean_Widget_elabWidgetInstanceSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__8 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__8_value;
static const lean_ctor_object l_Lean_Widget_elabWidgetInstanceSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__8_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__9 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__9_value;
static const lean_string_object l_Lean_Widget_elabWidgetInstanceSpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__10 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__10_value;
static const lean_string_object l_Lean_Widget_elabWidgetInstanceSpec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Widget_elabWidgetInstanceSpec___closed__11 = (const lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_addWidgetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "addWidgetSpec"};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__0 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__0_value;
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 146, 251, 200, 206, 220, 208, 83)}};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__1 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__1_value;
static const lean_string_object l_Lean_Widget_addWidgetSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__2 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__2_value;
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__3_value_aux_2),((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__3 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__3_value;
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__3_value)}};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__4 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__4_value;
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__4_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__19_value)}};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__5 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__5_value;
static const lean_ctor_object l_Lean_Widget_addWidgetSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__0_value),((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__1_value),((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__5_value)}};
static const lean_object* l_Lean_Widget_addWidgetSpec___closed__6 = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_addWidgetSpec = (const lean_object*)&l_Lean_Widget_addWidgetSpec___closed__6_value;
static const lean_string_object l_Lean_Widget_eraseWidgetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "eraseWidgetSpec"};
static const lean_object* l_Lean_Widget_eraseWidgetSpec___closed__0 = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__0_value;
static const lean_ctor_object l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_eraseWidgetSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 58, 73, 174, 184, 82, 104, 4)}};
static const lean_object* l_Lean_Widget_eraseWidgetSpec___closed__1 = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__1_value;
static const lean_string_object l_Lean_Widget_eraseWidgetSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Widget_eraseWidgetSpec___closed__2 = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__2_value;
static const lean_ctor_object l_Lean_Widget_eraseWidgetSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__2_value)}};
static const lean_object* l_Lean_Widget_eraseWidgetSpec___closed__3 = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__3_value;
static const lean_ctor_object l_Lean_Widget_eraseWidgetSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__3_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__8_value)}};
static const lean_object* l_Lean_Widget_eraseWidgetSpec___closed__4 = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__4_value;
static const lean_ctor_object l_Lean_Widget_eraseWidgetSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__0_value),((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__1_value),((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__4_value)}};
static const lean_object* l_Lean_Widget_eraseWidgetSpec___closed__5 = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_eraseWidgetSpec = (const lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__5_value;
static const lean_string_object l_Lean_Widget_showWidgetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "showWidgetSpec"};
static const lean_object* l_Lean_Widget_showWidgetSpec___closed__0 = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__0_value;
static const lean_ctor_object l_Lean_Widget_showWidgetSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_showWidgetSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_showWidgetSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 169, 125, 185, 204, 106, 221, 205)}};
static const lean_object* l_Lean_Widget_showWidgetSpec___closed__1 = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__1_value;
static const lean_string_object l_Lean_Widget_showWidgetSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Widget_showWidgetSpec___closed__2 = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__2_value;
static const lean_ctor_object l_Lean_Widget_showWidgetSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Widget_showWidgetSpec___closed__3 = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__3_value;
static const lean_ctor_object l_Lean_Widget_showWidgetSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__3_value),((lean_object*)&l_Lean_Widget_addWidgetSpec___closed__6_value),((lean_object*)&l_Lean_Widget_eraseWidgetSpec___closed__5_value)}};
static const lean_object* l_Lean_Widget_showWidgetSpec___closed__4 = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__4_value;
static const lean_ctor_object l_Lean_Widget_showWidgetSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__0_value),((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__1_value),((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__4_value)}};
static const lean_object* l_Lean_Widget_showWidgetSpec___closed__5 = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_showWidgetSpec = (const lean_object*)&l_Lean_Widget_showWidgetSpec___closed__5_value;
static const lean_string_object l_Lean_Widget_showPanelWidgetsCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "showPanelWidgetsCmd"};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__0 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__0_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 207, 30, 126, 74, 89, 231, 190)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__1 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__1_value;
static const lean_string_object l_Lean_Widget_showPanelWidgetsCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "show_panel_widgets "};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__2 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__2_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__2_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__3 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__3_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__10_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__4 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__4_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__3_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__4_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__5 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__5_value;
static const lean_string_object l_Lean_Widget_showPanelWidgetsCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__6 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__6_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__6_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__7 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__7_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_Widget_showWidgetSpec___closed__5_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__6_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__8 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__8_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__5_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__8_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__9 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__9_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_elabWidgetInstanceSpec___closed__11_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__10 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__10_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__9_value),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__10_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__11 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__11_value;
static const lean_ctor_object l_Lean_Widget_showPanelWidgetsCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__11_value)}};
static const lean_object* l_Lean_Widget_showPanelWidgetsCmd___closed__12 = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_showPanelWidgetsCmd = (const lean_object*)&l_Lean_Widget_showPanelWidgetsCmd___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 220, 71, 116, 84, 119, 12, 45)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "failed to compile expression, it contains metavariables"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5_value),LEAN_SCALAR_PTR_LITERAL(222, 167, 125, 136, 228, 207, 28, 37)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1 = (const lean_object*)&l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_widgetCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "widgetCmd"};
static const lean_object* l_Lean_Widget_widgetCmd___closed__0 = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__0_value;
static const lean_ctor_object l_Lean_Widget_widgetCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_widgetCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_widgetCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_widgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 247, 198, 226, 79, 16, 223, 88)}};
static const lean_object* l_Lean_Widget_widgetCmd___closed__1 = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__1_value;
static const lean_string_object l_Lean_Widget_widgetCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "#widget "};
static const lean_object* l_Lean_Widget_widgetCmd___closed__2 = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__2_value;
static const lean_ctor_object l_Lean_Widget_widgetCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetCmd___closed__2_value)}};
static const lean_object* l_Lean_Widget_widgetCmd___closed__3 = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__3_value;
static const lean_ctor_object l_Lean_Widget_widgetCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__5_value),((lean_object*)&l_Lean_Widget_widgetCmd___closed__3_value),((lean_object*)&l_Lean_Widget_widgetInstanceSpec___closed__19_value)}};
static const lean_object* l_Lean_Widget_widgetCmd___closed__4 = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__4_value;
static const lean_ctor_object l_Lean_Widget_widgetCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_widgetCmd___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Widget_widgetCmd___closed__4_value)}};
static const lean_object* l_Lean_Widget_widgetCmd___closed__5 = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_widgetCmd = (const lean_object*)&l_Lean_Widget_widgetCmd___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Array_mkArray0___redArg();
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14));
v___x_77_ = l_String_toRawSubstring_x27(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_122_ = l_String_toRawSubstring_x27(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49));
v___x_157_ = l_String_toRawSubstring_x27(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59));
v___x_178_ = l_String_toRawSubstring_x27(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62));
v___x_183_ = l_String_toRawSubstring_x27(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
v___x_215_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_216_ = l_Lean_mkConst(v___x_215_, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(lean_object* v_mod_226_, lean_object* v_props_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_toCold_235_; lean_object* v_ref_236_; lean_object* v_quotContext_237_; lean_object* v_currMacroScope_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___y_261_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_toCold_235_ = lean_ctor_get(v_a_232_, 0);
v_ref_236_ = lean_ctor_get(v_a_232_, 2);
v_quotContext_237_ = lean_ctor_get(v_toCold_235_, 8);
v_currMacroScope_238_ = lean_ctor_get(v_toCold_235_, 9);
v___x_239_ = 0;
v___x_240_ = l_Lean_SourceInfo_fromRef(v_ref_236_, v___x_239_);
v___x_241_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3));
v___x_242_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4));
lean_inc_n(v___x_240_, 5);
v___x_243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_245_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
v___x_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_240_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
v___x_247_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9));
v___x_248_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11));
v___x_249_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13));
v___x_250_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15);
v___x_251_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16));
lean_inc(v_currMacroScope_238_);
lean_inc(v_quotContext_237_);
v___x_252_ = l_Lean_addMacroScope(v_quotContext_237_, v___x_251_, v_currMacroScope_238_);
v___x_253_ = lean_box(0);
v___x_254_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18));
v___x_255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_255_, 0, v___x_240_);
lean_ctor_set(v___x_255_, 1, v___x_250_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
lean_inc_ref(v___x_246_);
v___x_256_ = l_Lean_Syntax_node2(v___x_240_, v___x_249_, v___x_255_, v___x_246_);
v___x_257_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20));
v___x_258_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21));
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_240_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_325_ = l_Lean_TSyntax_getId(v_mod_226_);
lean_inc(v___x_325_);
v___x_326_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_253_, v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_quoteNameMk(v___x_325_);
v___y_261_ = v___x_327_;
goto v___jp_260_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v___x_325_);
v_val_328_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_326_, 1);
v___x_329_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79));
v___x_330_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80));
v___x_331_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58));
v___x_332_ = lean_string_intercalate(v___x_331_, v_val_328_);
v___x_333_ = lean_string_append(v___x_330_, v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_box(2);
v___x_335_ = l_Lean_Syntax_mkNameLit(v___x_333_, v___x_334_);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_mk_empty_array_with_capacity(v___x_336_);
v___x_338_ = lean_array_push(v___x_337_, v___x_335_);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v___x_334_);
lean_ctor_set(v___x_339_, 1, v___x_329_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
v___y_261_ = v___x_339_;
goto v___jp_260_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; 
lean_inc_ref_n(v___x_246_, 15);
lean_inc_ref_n(v___x_259_, 2);
lean_inc_n(v___x_240_, 31);
v___x_262_ = l_Lean_Syntax_node3(v___x_240_, v___x_257_, v___x_259_, v___x_246_, v___y_261_);
v___x_263_ = l_Lean_Syntax_node3(v___x_240_, v___x_244_, v___x_246_, v___x_246_, v___x_262_);
v___x_264_ = l_Lean_Syntax_node2(v___x_240_, v___x_248_, v___x_256_, v___x_263_);
v___x_265_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23);
v___x_266_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24));
lean_inc_n(v_currMacroScope_238_, 5);
lean_inc_n(v_quotContext_237_, 5);
v___x_267_ = l_Lean_addMacroScope(v_quotContext_237_, v___x_266_, v_currMacroScope_238_);
v___x_268_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_268_, 0, v___x_240_);
lean_ctor_set(v___x_268_, 1, v___x_265_);
lean_ctor_set(v___x_268_, 2, v___x_267_);
lean_ctor_set(v___x_268_, 3, v___x_253_);
lean_inc_ref(v___x_268_);
v___x_269_ = l_Lean_Syntax_node2(v___x_240_, v___x_249_, v___x_268_, v___x_246_);
v___x_270_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26));
v___x_271_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28));
v___x_272_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30));
v___x_273_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31));
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_240_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33));
v___x_276_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35);
v___x_277_ = lean_box(0);
v___x_278_ = l_Lean_addMacroScope(v_quotContext_237_, v___x_277_, v_currMacroScope_238_);
v___x_279_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46));
v___x_280_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_280_, 0, v___x_240_);
lean_ctor_set(v___x_280_, 1, v___x_276_);
lean_ctor_set(v___x_280_, 2, v___x_278_);
lean_ctor_set(v___x_280_, 3, v___x_279_);
v___x_281_ = l_Lean_Syntax_node1(v___x_240_, v___x_275_, v___x_280_);
v___x_282_ = l_Lean_Syntax_node2(v___x_240_, v___x_272_, v___x_274_, v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_284_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_285_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
v___x_286_ = l_Lean_addMacroScope(v_quotContext_237_, v___x_285_, v_currMacroScope_238_);
v___x_287_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
v___x_288_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_288_, 0, v___x_240_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
lean_ctor_set(v___x_288_, 2, v___x_286_);
lean_ctor_set(v___x_288_, 3, v___x_287_);
v___x_289_ = l_Lean_Syntax_node1(v___x_240_, v___x_244_, v_mod_226_);
v___x_290_ = l_Lean_Syntax_node2(v___x_240_, v___x_283_, v___x_288_, v___x_289_);
v___x_291_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57));
v___x_292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_240_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Lean_Syntax_node3(v___x_240_, v___x_271_, v___x_282_, v___x_290_, v___x_292_);
v___x_294_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58));
v___x_295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_240_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_Syntax_node3(v___x_240_, v___x_270_, v___x_293_, v___x_295_, v___x_268_);
v___x_297_ = l_Lean_Syntax_node3(v___x_240_, v___x_257_, v___x_259_, v___x_246_, v___x_296_);
v___x_298_ = l_Lean_Syntax_node3(v___x_240_, v___x_244_, v___x_246_, v___x_246_, v___x_297_);
v___x_299_ = l_Lean_Syntax_node2(v___x_240_, v___x_248_, v___x_269_, v___x_298_);
v___x_300_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60);
v___x_301_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61));
v___x_302_ = l_Lean_addMacroScope(v_quotContext_237_, v___x_301_, v_currMacroScope_238_);
v___x_303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_303_, 0, v___x_240_);
lean_ctor_set(v___x_303_, 1, v___x_300_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
lean_ctor_set(v___x_303_, 3, v___x_253_);
v___x_304_ = l_Lean_Syntax_node2(v___x_240_, v___x_249_, v___x_303_, v___x_246_);
v___x_305_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63);
v___x_306_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67));
v___x_307_ = l_Lean_addMacroScope(v_quotContext_237_, v___x_306_, v_currMacroScope_238_);
v___x_308_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70));
v___x_309_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_309_, 0, v___x_240_);
lean_ctor_set(v___x_309_, 1, v___x_305_);
lean_ctor_set(v___x_309_, 2, v___x_307_);
lean_ctor_set(v___x_309_, 3, v___x_308_);
v___x_310_ = l_Lean_Syntax_node1(v___x_240_, v___x_244_, v_props_227_);
v___x_311_ = l_Lean_Syntax_node2(v___x_240_, v___x_283_, v___x_309_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node3(v___x_240_, v___x_257_, v___x_259_, v___x_246_, v___x_311_);
v___x_313_ = l_Lean_Syntax_node3(v___x_240_, v___x_244_, v___x_246_, v___x_246_, v___x_312_);
v___x_314_ = l_Lean_Syntax_node2(v___x_240_, v___x_248_, v___x_304_, v___x_313_);
v___x_315_ = l_Lean_Syntax_node5(v___x_240_, v___x_244_, v___x_264_, v___x_246_, v___x_299_, v___x_246_, v___x_314_);
v___x_316_ = l_Lean_Syntax_node1(v___x_240_, v___x_247_, v___x_315_);
v___x_317_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72));
v___x_318_ = l_Lean_Syntax_node1(v___x_240_, v___x_317_, v___x_246_);
v___x_319_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73));
v___x_320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_240_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Lean_Syntax_node6(v___x_240_, v___x_241_, v___x_243_, v___x_246_, v___x_316_, v___x_318_, v___x_246_, v___x_320_);
v___x_322_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77);
v___x_323_ = 1;
v___x_324_ = l_Lean_Elab_Term_elabTerm(v___x_321_, v___x_322_, v___x_323_, v___x_323_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___boxed(lean_object* v_mod_340_, lean_object* v_props_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_340_, v_props_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
v___x_351_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg(){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___boxed(lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(lean_object* v_00_u03b1_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___boxed(lean_object* v_00_u03b1_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(v_00_u03b1_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_375_;
}
}
static lean_object* _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__0));
v___x_378_ = l_String_toRawSubstring_x27(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec(lean_object* v_x_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v_x_399_);
v___x_408_ = l_Lean_Syntax_isOfKind(v_x_399_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec(v_x_399_);
v___x_409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v_mod_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v_mod_411_ = l_Lean_Syntax_getArg(v_x_399_, v___x_410_);
v___x_412_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v_mod_411_);
v___x_413_ = l_Lean_Syntax_isOfKind(v_mod_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec(v_mod_411_);
lean_dec(v_x_399_);
v___x_414_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_399_, v___x_415_);
lean_dec(v_x_399_);
lean_inc(v___x_416_);
v___x_417_ = l_Lean_Syntax_matchesNull(v___x_416_, v___x_410_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_416_);
v___x_419_ = l_Lean_Syntax_matchesNull(v___x_416_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec(v___x_416_);
lean_dec(v_mod_411_);
v___x_420_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_420_;
}
else
{
lean_object* v_props_421_; lean_object* v___x_422_; 
v_props_421_ = l_Lean_Syntax_getArg(v___x_416_, v___x_415_);
lean_dec(v___x_416_);
v___x_422_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_411_, v_props_421_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_422_;
}
}
else
{
lean_object* v_toCold_423_; lean_object* v_ref_424_; lean_object* v_quotContext_425_; lean_object* v_currMacroScope_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v___x_416_);
v_toCold_423_ = lean_ctor_get(v_a_404_, 0);
v_ref_424_ = lean_ctor_get(v_a_404_, 2);
v_quotContext_425_ = lean_ctor_get(v_toCold_423_, 8);
v_currMacroScope_426_ = lean_ctor_get(v_toCold_423_, 9);
v___x_427_ = 0;
v___x_428_ = l_Lean_SourceInfo_fromRef(v_ref_424_, v___x_427_);
v___x_429_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_430_ = lean_obj_once(&l_Lean_Widget_elabWidgetInstanceSpec___closed__1, &l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once, _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1);
v___x_431_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__4));
lean_inc(v_currMacroScope_426_);
lean_inc(v_quotContext_425_);
v___x_432_ = l_Lean_addMacroScope(v_quotContext_425_, v___x_431_, v_currMacroScope_426_);
v___x_433_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__7));
lean_inc_n(v___x_428_, 6);
v___x_434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_434_, 0, v___x_428_);
lean_ctor_set(v___x_434_, 1, v___x_430_);
lean_ctor_set(v___x_434_, 2, v___x_432_);
lean_ctor_set(v___x_434_, 3, v___x_433_);
v___x_435_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_436_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__9));
v___x_437_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__10));
v___x_438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_428_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
v___x_440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_440_, 0, v___x_428_);
lean_ctor_set(v___x_440_, 1, v___x_435_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
v___x_441_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__11));
v___x_442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_428_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_Syntax_node3(v___x_428_, v___x_436_, v___x_438_, v___x_440_, v___x_442_);
v___x_444_ = l_Lean_Syntax_node1(v___x_428_, v___x_435_, v___x_443_);
v___x_445_ = l_Lean_Syntax_node2(v___x_428_, v___x_429_, v___x_434_, v___x_444_);
v___x_446_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_411_, v___x_445_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec___boxed(lean_object* v_x_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Widget_elabWidgetInstanceSpec(v_x_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg___boxed(lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(lean_object* v_00_u03b1_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___boxed(lean_object* v_00_u03b1_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(v_00_u03b1_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(lean_object* v_e_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Expr_hasMVar(v_e_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_e_564_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v_mctx_570_; lean_object* v___x_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_574_; lean_object* v_cache_575_; lean_object* v_zetaDeltaFVarIds_576_; lean_object* v_postponed_577_; lean_object* v_diag_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_587_; 
v___x_569_ = lean_st_ref_get(v___y_565_);
v_mctx_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_mctx_570_);
lean_dec(v___x_569_);
v___x_571_ = l_Lean_instantiateMVarsCore(v_mctx_570_, v_e_564_);
v_fst_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_573_);
lean_dec_ref(v___x_571_);
v___x_574_ = lean_st_ref_take(v___y_565_);
v_cache_575_ = lean_ctor_get(v___x_574_, 1);
v_zetaDeltaFVarIds_576_ = lean_ctor_get(v___x_574_, 2);
v_postponed_577_ = lean_ctor_get(v___x_574_, 3);
v_diag_578_ = lean_ctor_get(v___x_574_, 4);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_574_, 0);
lean_dec(v_unused_588_);
v___x_580_ = v___x_574_;
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_diag_578_);
lean_inc(v_postponed_577_);
lean_inc(v_zetaDeltaFVarIds_576_);
lean_inc(v_cache_575_);
lean_dec(v___x_574_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_snd_573_);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_snd_573_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_cache_575_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_zetaDeltaFVarIds_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_postponed_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_diag_578_);
v___x_583_ = v_reuseFailAlloc_586_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_st_ref_put(v___y_565_, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v_fst_572_);
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(lean_object* v_e_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_589_, v___y_590_);
lean_dec(v___y_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(lean_object* v_e_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_593_, v___y_597_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(lean_object* v_e_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(v_e_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(uint64_t v_k_611_, lean_object* v_t_612_){
_start:
{
if (lean_obj_tag(v_t_612_) == 0)
{
lean_object* v_k_613_; lean_object* v_v_614_; lean_object* v_l_615_; lean_object* v_r_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_1273_; 
v_k_613_ = lean_ctor_get(v_t_612_, 1);
v_v_614_ = lean_ctor_get(v_t_612_, 2);
v_l_615_ = lean_ctor_get(v_t_612_, 3);
v_r_616_ = lean_ctor_get(v_t_612_, 4);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_t_612_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_t_612_, 0);
lean_dec(v_unused_1274_);
v___x_618_ = v_t_612_;
v_isShared_619_ = v_isSharedCheck_1273_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_r_616_);
lean_inc(v_l_615_);
lean_inc(v_v_614_);
lean_inc(v_k_613_);
lean_dec(v_t_612_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_1273_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint64_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unbox_uint64(v_k_613_);
v___x_621_ = lean_uint64_dec_lt(v_k_611_, v___x_620_);
if (v___x_621_ == 0)
{
uint64_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_unbox_uint64(v_k_613_);
v___x_623_ = lean_uint64_dec_eq(v_k_611_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v_impl_624_; lean_object* v___x_625_; 
v_impl_624_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_611_, v_r_616_);
v___x_625_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_624_) == 0)
{
if (lean_obj_tag(v_l_615_) == 0)
{
lean_object* v_size_626_; lean_object* v_size_627_; lean_object* v_k_628_; lean_object* v_v_629_; lean_object* v_l_630_; lean_object* v_r_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_size_626_ = lean_ctor_get(v_impl_624_, 0);
lean_inc(v_size_626_);
v_size_627_ = lean_ctor_get(v_l_615_, 0);
v_k_628_ = lean_ctor_get(v_l_615_, 1);
v_v_629_ = lean_ctor_get(v_l_615_, 2);
v_l_630_ = lean_ctor_get(v_l_615_, 3);
v_r_631_ = lean_ctor_get(v_l_615_, 4);
lean_inc(v_r_631_);
v___x_632_ = lean_unsigned_to_nat(3u);
v___x_633_ = lean_nat_mul(v___x_632_, v_size_626_);
v___x_634_ = lean_nat_dec_lt(v___x_633_, v_size_627_);
lean_dec(v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
lean_dec(v_r_631_);
v___x_635_ = lean_nat_add(v___x_625_, v_size_627_);
v___x_636_ = lean_nat_add(v___x_635_, v_size_626_);
lean_dec(v_size_626_);
lean_dec(v___x_635_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_impl_624_);
lean_ctor_set(v___x_618_, 0, v___x_636_);
v___x_638_ = v___x_618_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_impl_624_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_705_; 
lean_inc(v_l_630_);
lean_inc(v_v_629_);
lean_inc(v_k_628_);
lean_inc(v_size_627_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_706_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_l_615_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_l_615_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_710_);
v___x_641_ = v_l_615_;
v_isShared_642_ = v_isSharedCheck_705_;
goto v_resetjp_640_;
}
else
{
lean_dec(v_l_615_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_705_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_size_643_; lean_object* v_size_644_; lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v_l_647_; lean_object* v_r_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_size_643_ = lean_ctor_get(v_l_630_, 0);
v_size_644_ = lean_ctor_get(v_r_631_, 0);
v_k_645_ = lean_ctor_get(v_r_631_, 1);
v_v_646_ = lean_ctor_get(v_r_631_, 2);
v_l_647_ = lean_ctor_get(v_r_631_, 3);
v_r_648_ = lean_ctor_get(v_r_631_, 4);
v___x_649_ = lean_unsigned_to_nat(2u);
v___x_650_ = lean_nat_mul(v___x_649_, v_size_643_);
v___x_651_ = lean_nat_dec_lt(v_size_644_, v___x_650_);
lean_dec(v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_680_; 
lean_inc(v_r_648_);
lean_inc(v_l_647_);
lean_inc(v_v_646_);
lean_inc(v_k_645_);
v_isSharedCheck_680_ = !lean_is_exclusive(v_r_631_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_681_ = lean_ctor_get(v_r_631_, 4);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_r_631_, 3);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_631_, 2);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_r_631_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_r_631_, 0);
lean_dec(v_unused_685_);
v___x_653_ = v_r_631_;
v_isShared_654_ = v_isSharedCheck_680_;
goto v_resetjp_652_;
}
else
{
lean_dec(v_r_631_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_680_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___x_668_; lean_object* v___y_670_; 
v___x_655_ = lean_nat_add(v___x_625_, v_size_627_);
lean_dec(v_size_627_);
v___x_656_ = lean_nat_add(v___x_655_, v_size_626_);
lean_dec(v___x_655_);
v___x_668_ = lean_nat_add(v___x_625_, v_size_643_);
if (lean_obj_tag(v_l_647_) == 0)
{
lean_object* v_size_678_; 
v_size_678_ = lean_ctor_get(v_l_647_, 0);
lean_inc(v_size_678_);
v___y_670_ = v_size_678_;
goto v___jp_669_;
}
else
{
lean_object* v___x_679_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___y_670_ = v___x_679_;
goto v___jp_669_;
}
v___jp_657_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_nat_add(v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec(v___y_659_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v_impl_624_);
lean_ctor_set(v___x_653_, 3, v_r_648_);
lean_ctor_set(v___x_653_, 2, v_v_614_);
lean_ctor_set(v___x_653_, 1, v_k_613_);
lean_ctor_set(v___x_653_, 0, v___x_661_);
v___x_663_ = v___x_653_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_r_648_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_impl_624_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v___x_663_);
lean_ctor_set(v___x_641_, 3, v___y_658_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_656_);
v___x_665_ = v___x_641_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v___y_658_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_nat_add(v___x_668_, v___y_670_);
lean_dec(v___y_670_);
lean_dec(v___x_668_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_l_647_);
lean_ctor_set(v___x_618_, 3, v_l_630_);
lean_ctor_set(v___x_618_, 2, v_v_629_);
lean_ctor_set(v___x_618_, 1, v_k_628_);
lean_ctor_set(v___x_618_, 0, v___x_671_);
v___x_673_ = v___x_618_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_l_647_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; 
v___x_674_ = lean_nat_add(v___x_625_, v_size_626_);
lean_dec(v_size_626_);
if (lean_obj_tag(v_r_648_) == 0)
{
lean_object* v_size_675_; 
v_size_675_ = lean_ctor_get(v_r_648_, 0);
lean_inc(v_size_675_);
v___y_658_ = v___x_673_;
v___y_659_ = v___x_674_;
v___y_660_ = v_size_675_;
goto v___jp_657_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___y_658_ = v___x_673_;
v___y_659_ = v___x_674_;
v___y_660_ = v___x_676_;
goto v___jp_657_;
}
}
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_del_object(v___x_618_);
v___x_686_ = lean_nat_add(v___x_625_, v_size_627_);
lean_dec(v_size_627_);
v___x_687_ = lean_nat_add(v___x_686_, v_size_626_);
lean_dec(v___x_686_);
v___x_688_ = lean_nat_add(v___x_625_, v_size_626_);
lean_dec(v_size_626_);
v___x_689_ = lean_nat_add(v___x_688_, v_size_644_);
lean_dec(v___x_688_);
lean_inc_ref(v_impl_624_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_impl_624_);
lean_ctor_set(v___x_641_, 3, v_r_631_);
lean_ctor_set(v___x_641_, 2, v_v_614_);
lean_ctor_set(v___x_641_, 1, v_k_613_);
lean_ctor_set(v___x_641_, 0, v___x_689_);
v___x_691_ = v___x_641_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_r_631_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_impl_624_);
v___x_691_ = v_reuseFailAlloc_704_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_isSharedCheck_698_ = !lean_is_exclusive(v_impl_624_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; 
v_unused_699_ = lean_ctor_get(v_impl_624_, 4);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_impl_624_, 3);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_impl_624_, 2);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_impl_624_, 1);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_impl_624_, 0);
lean_dec(v_unused_703_);
v___x_693_ = v_impl_624_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_dec(v_impl_624_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v___x_691_);
lean_ctor_set(v___x_693_, 3, v_l_630_);
lean_ctor_set(v___x_693_, 2, v_v_629_);
lean_ctor_set(v___x_693_, 1, v_k_628_);
lean_ctor_set(v___x_693_, 0, v___x_687_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v___x_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v_size_711_ = lean_ctor_get(v_impl_624_, 0);
lean_inc(v_size_711_);
v___x_712_ = lean_nat_add(v___x_625_, v_size_711_);
lean_dec(v_size_711_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_impl_624_);
lean_ctor_set(v___x_618_, 0, v___x_712_);
v___x_714_ = v___x_618_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_impl_624_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
if (lean_obj_tag(v_l_615_) == 0)
{
lean_object* v_l_716_; 
v_l_716_ = lean_ctor_get(v_l_615_, 3);
if (lean_obj_tag(v_l_716_) == 0)
{
lean_object* v_r_717_; 
lean_inc_ref(v_l_716_);
v_r_717_ = lean_ctor_get(v_l_615_, 4);
lean_inc(v_r_717_);
if (lean_obj_tag(v_r_717_) == 0)
{
lean_object* v_size_718_; lean_object* v_k_719_; lean_object* v_v_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_733_; 
v_size_718_ = lean_ctor_get(v_l_615_, 0);
v_k_719_ = lean_ctor_get(v_l_615_, 1);
v_v_720_ = lean_ctor_get(v_l_615_, 2);
v_isSharedCheck_733_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; 
v_unused_734_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_735_);
v___x_722_ = v_l_615_;
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_v_720_);
lean_inc(v_k_719_);
lean_inc(v_size_718_);
lean_dec(v_l_615_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_size_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_size_724_ = lean_ctor_get(v_r_717_, 0);
v___x_725_ = lean_nat_add(v___x_625_, v_size_718_);
lean_dec(v_size_718_);
v___x_726_ = lean_nat_add(v___x_625_, v_size_724_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 4, v_impl_624_);
lean_ctor_set(v___x_722_, 3, v_r_717_);
lean_ctor_set(v___x_722_, 2, v_v_614_);
lean_ctor_set(v___x_722_, 1, v_k_613_);
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_r_717_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_impl_624_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_728_);
lean_ctor_set(v___x_618_, 3, v_l_716_);
lean_ctor_set(v___x_618_, 2, v_v_720_);
lean_ctor_set(v___x_618_, 1, v_k_719_);
lean_ctor_set(v___x_618_, 0, v___x_725_);
v___x_730_ = v___x_618_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_720_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_l_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_k_736_; lean_object* v_v_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_k_736_ = lean_ctor_get(v_l_615_, 1);
v_v_737_ = lean_ctor_get(v_l_615_, 2);
v_isSharedCheck_748_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; lean_object* v_unused_751_; 
v_unused_749_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_751_);
v___x_739_ = v_l_615_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_v_737_);
lean_inc(v_k_736_);
lean_dec(v_l_615_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_unsigned_to_nat(3u);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 3, v_r_717_);
lean_ctor_set(v___x_739_, 2, v_v_614_);
lean_ctor_set(v___x_739_, 1, v_k_613_);
lean_ctor_set(v___x_739_, 0, v___x_625_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_r_717_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_r_717_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_743_);
lean_ctor_set(v___x_618_, 3, v_l_716_);
lean_ctor_set(v___x_618_, 2, v_v_737_);
lean_ctor_set(v___x_618_, 1, v_k_736_);
lean_ctor_set(v___x_618_, 0, v___x_741_);
v___x_745_ = v___x_618_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_736_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_737_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_l_716_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v_r_752_; 
v_r_752_ = lean_ctor_get(v_l_615_, 4);
lean_inc(v_r_752_);
if (lean_obj_tag(v_r_752_) == 0)
{
lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_777_; 
lean_inc(v_l_716_);
v_k_753_ = lean_ctor_get(v_l_615_, 1);
v_v_754_ = lean_ctor_get(v_l_615_, 2);
v_isSharedCheck_777_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; lean_object* v_unused_780_; 
v_unused_778_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_780_);
v___x_756_ = v_l_615_;
v_isShared_757_ = v_isSharedCheck_777_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_v_754_);
lean_inc(v_k_753_);
lean_dec(v_l_615_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_777_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_k_758_; lean_object* v_v_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_773_; 
v_k_758_ = lean_ctor_get(v_r_752_, 1);
v_v_759_ = lean_ctor_get(v_r_752_, 2);
v_isSharedCheck_773_ = !lean_is_exclusive(v_r_752_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_774_ = lean_ctor_get(v_r_752_, 4);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_752_, 3);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_752_, 0);
lean_dec(v_unused_776_);
v___x_761_ = v_r_752_;
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_v_759_);
lean_inc(v_k_758_);
lean_dec(v_r_752_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(3u);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v_l_716_);
lean_ctor_set(v___x_761_, 3, v_l_716_);
lean_ctor_set(v___x_761_, 2, v_v_754_);
lean_ctor_set(v___x_761_, 1, v_k_753_);
lean_ctor_set(v___x_761_, 0, v___x_625_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_l_716_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_l_716_);
v___x_765_ = v_reuseFailAlloc_772_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_l_716_);
lean_ctor_set(v___x_756_, 2, v_v_614_);
lean_ctor_set(v___x_756_, 1, v_k_613_);
lean_ctor_set(v___x_756_, 0, v___x_625_);
v___x_767_ = v___x_756_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_l_716_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_716_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_767_);
lean_ctor_set(v___x_618_, 3, v___x_765_);
lean_ctor_set(v___x_618_, 2, v_v_759_);
lean_ctor_set(v___x_618_, 1, v_k_758_);
lean_ctor_set(v___x_618_, 0, v___x_763_);
v___x_769_ = v___x_618_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_unsigned_to_nat(2u);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_r_752_);
lean_ctor_set(v___x_618_, 0, v___x_781_);
v___x_783_ = v___x_618_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_r_752_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_786_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_l_615_);
lean_ctor_set(v___x_618_, 0, v___x_625_);
v___x_786_ = v___x_618_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_l_615_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_del_object(v___x_618_);
lean_dec(v_v_614_);
lean_dec(v_k_613_);
if (lean_obj_tag(v_l_615_) == 0)
{
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_size_788_; lean_object* v_k_789_; lean_object* v_v_790_; lean_object* v_l_791_; lean_object* v_r_792_; lean_object* v_size_793_; lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v_l_796_; lean_object* v_r_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_size_788_ = lean_ctor_get(v_l_615_, 0);
v_k_789_ = lean_ctor_get(v_l_615_, 1);
v_v_790_ = lean_ctor_get(v_l_615_, 2);
v_l_791_ = lean_ctor_get(v_l_615_, 3);
v_r_792_ = lean_ctor_get(v_l_615_, 4);
lean_inc(v_r_792_);
v_size_793_ = lean_ctor_get(v_r_616_, 0);
v_k_794_ = lean_ctor_get(v_r_616_, 1);
v_v_795_ = lean_ctor_get(v_r_616_, 2);
v_l_796_ = lean_ctor_get(v_r_616_, 3);
lean_inc(v_l_796_);
v_r_797_ = lean_ctor_get(v_r_616_, 4);
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_dec_lt(v_size_788_, v_size_793_);
if (v___x_799_ == 0)
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_935_; 
lean_inc(v_l_791_);
lean_inc(v_v_790_);
lean_inc(v_k_789_);
v_isSharedCheck_935_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; lean_object* v_unused_940_; 
v_unused_936_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_615_, 2);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_l_615_, 1);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_940_);
v___x_801_ = v_l_615_;
v_isShared_802_ = v_isSharedCheck_935_;
goto v_resetjp_800_;
}
else
{
lean_dec(v_l_615_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_935_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v_tree_804_; 
v___x_803_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_789_, v_v_790_, v_l_791_, v_r_792_);
v_tree_804_ = lean_ctor_get(v___x_803_, 2);
lean_inc(v_tree_804_);
if (lean_obj_tag(v_tree_804_) == 0)
{
lean_object* v_k_805_; lean_object* v_v_806_; lean_object* v_size_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_k_805_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_k_805_);
v_v_806_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_v_806_);
lean_dec_ref(v___x_803_);
v_size_807_ = lean_ctor_get(v_tree_804_, 0);
v___x_808_ = lean_unsigned_to_nat(3u);
v___x_809_ = lean_nat_mul(v___x_808_, v_size_807_);
v___x_810_ = lean_nat_dec_lt(v___x_809_, v_size_793_);
lean_dec(v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec(v_l_796_);
v___x_811_ = lean_nat_add(v___x_798_, v_size_807_);
v___x_812_ = lean_nat_add(v___x_811_, v_size_793_);
lean_dec(v___x_811_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v_r_616_);
lean_ctor_set(v___x_801_, 3, v_tree_804_);
lean_ctor_set(v___x_801_, 2, v_v_806_);
lean_ctor_set(v___x_801_, 1, v_k_805_);
lean_ctor_set(v___x_801_, 0, v___x_812_);
v___x_814_ = v___x_801_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_806_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_tree_804_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_r_616_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_870_; 
lean_inc(v_r_797_);
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_inc(v_size_793_);
v_isSharedCheck_870_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_871_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_r_616_, 2);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_r_616_, 1);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_875_);
v___x_817_ = v_r_616_;
v_isShared_818_ = v_isSharedCheck_870_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_r_616_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_870_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_size_819_; lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v_l_822_; lean_object* v_r_823_; lean_object* v_size_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_size_819_ = lean_ctor_get(v_l_796_, 0);
v_k_820_ = lean_ctor_get(v_l_796_, 1);
v_v_821_ = lean_ctor_get(v_l_796_, 2);
v_l_822_ = lean_ctor_get(v_l_796_, 3);
v_r_823_ = lean_ctor_get(v_l_796_, 4);
v_size_824_ = lean_ctor_get(v_r_797_, 0);
v___x_825_ = lean_unsigned_to_nat(2u);
v___x_826_ = lean_nat_mul(v___x_825_, v_size_824_);
v___x_827_ = lean_nat_dec_lt(v_size_819_, v___x_826_);
lean_dec(v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_855_; 
lean_inc(v_r_823_);
lean_inc(v_l_822_);
lean_inc(v_v_821_);
lean_inc(v_k_820_);
v_isSharedCheck_855_ = !lean_is_exclusive(v_l_796_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; 
v_unused_856_ = lean_ctor_get(v_l_796_, 4);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_l_796_, 3);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_l_796_, 2);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_l_796_, 1);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_l_796_, 0);
lean_dec(v_unused_860_);
v___x_829_ = v_l_796_;
v_isShared_830_ = v_isSharedCheck_855_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_l_796_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_855_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_845_; 
v___x_831_ = lean_nat_add(v___x_798_, v_size_807_);
v___x_832_ = lean_nat_add(v___x_831_, v_size_793_);
lean_dec(v_size_793_);
if (lean_obj_tag(v_l_822_) == 0)
{
lean_object* v_size_853_; 
v_size_853_ = lean_ctor_get(v_l_822_, 0);
lean_inc(v_size_853_);
v___y_845_ = v_size_853_;
goto v___jp_844_;
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___y_845_ = v___x_854_;
goto v___jp_844_;
}
v___jp_833_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_nat_add(v___y_834_, v___y_836_);
lean_dec(v___y_836_);
lean_dec(v___y_834_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 4, v_r_797_);
lean_ctor_set(v___x_829_, 3, v_r_823_);
lean_ctor_set(v___x_829_, 2, v_v_795_);
lean_ctor_set(v___x_829_, 1, v_k_794_);
lean_ctor_set(v___x_829_, 0, v___x_837_);
v___x_839_ = v___x_829_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_r_823_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_r_797_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 4, v___x_839_);
lean_ctor_set(v___x_817_, 3, v___y_835_);
lean_ctor_set(v___x_817_, 2, v_v_821_);
lean_ctor_set(v___x_817_, 1, v_k_820_);
lean_ctor_set(v___x_817_, 0, v___x_832_);
v___x_841_ = v___x_817_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_820_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_821_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v___y_835_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
v___jp_844_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_nat_add(v___x_831_, v___y_845_);
lean_dec(v___y_845_);
lean_dec(v___x_831_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v_l_822_);
lean_ctor_set(v___x_801_, 3, v_tree_804_);
lean_ctor_set(v___x_801_, 2, v_v_806_);
lean_ctor_set(v___x_801_, 1, v_k_805_);
lean_ctor_set(v___x_801_, 0, v___x_846_);
v___x_848_ = v___x_801_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_k_805_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_v_806_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_tree_804_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v_l_822_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; 
v___x_849_ = lean_nat_add(v___x_798_, v_size_824_);
if (lean_obj_tag(v_r_823_) == 0)
{
lean_object* v_size_850_; 
v_size_850_ = lean_ctor_get(v_r_823_, 0);
lean_inc(v_size_850_);
v___y_834_ = v___x_849_;
v___y_835_ = v___x_848_;
v___y_836_ = v_size_850_;
goto v___jp_833_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v___y_834_ = v___x_849_;
v___y_835_ = v___x_848_;
v___y_836_ = v___x_851_;
goto v___jp_833_;
}
}
}
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_861_ = lean_nat_add(v___x_798_, v_size_807_);
v___x_862_ = lean_nat_add(v___x_861_, v_size_793_);
lean_dec(v_size_793_);
v___x_863_ = lean_nat_add(v___x_861_, v_size_819_);
lean_dec(v___x_861_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 4, v_l_796_);
lean_ctor_set(v___x_817_, 3, v_tree_804_);
lean_ctor_set(v___x_817_, 2, v_v_806_);
lean_ctor_set(v___x_817_, 1, v_k_805_);
lean_ctor_set(v___x_817_, 0, v___x_863_);
v___x_865_ = v___x_817_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_k_805_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_v_806_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_tree_804_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_l_796_);
v___x_865_ = v_reuseFailAlloc_869_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v_r_797_);
lean_ctor_set(v___x_801_, 3, v___x_865_);
lean_ctor_set(v___x_801_, 2, v_v_795_);
lean_ctor_set(v___x_801_, 1, v_k_794_);
lean_ctor_set(v___x_801_, 0, v___x_862_);
v___x_867_ = v___x_801_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_r_797_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
else
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_929_; 
lean_inc(v_r_797_);
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_inc(v_size_793_);
v_isSharedCheck_929_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; 
v_unused_930_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_r_616_, 2);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_r_616_, 1);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_934_);
v___x_877_ = v_r_616_;
v_isShared_878_ = v_isSharedCheck_929_;
goto v_resetjp_876_;
}
else
{
lean_dec(v_r_616_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_929_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
if (lean_obj_tag(v_l_796_) == 0)
{
if (lean_obj_tag(v_r_797_) == 0)
{
lean_object* v_k_879_; lean_object* v_v_880_; lean_object* v_size_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v_k_879_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_k_879_);
v_v_880_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_v_880_);
lean_dec_ref(v___x_803_);
v_size_881_ = lean_ctor_get(v_l_796_, 0);
v___x_882_ = lean_nat_add(v___x_798_, v_size_793_);
lean_dec(v_size_793_);
v___x_883_ = lean_nat_add(v___x_798_, v_size_881_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 4, v_l_796_);
lean_ctor_set(v___x_877_, 3, v_tree_804_);
lean_ctor_set(v___x_877_, 2, v_v_880_);
lean_ctor_set(v___x_877_, 1, v_k_879_);
lean_ctor_set(v___x_877_, 0, v___x_883_);
v___x_885_ = v___x_877_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_879_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_880_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_tree_804_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_l_796_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v_r_797_);
lean_ctor_set(v___x_801_, 3, v___x_885_);
lean_ctor_set(v___x_801_, 2, v_v_795_);
lean_ctor_set(v___x_801_, 1, v_k_794_);
lean_ctor_set(v___x_801_, 0, v___x_882_);
v___x_887_ = v___x_801_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_r_797_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_k_890_; lean_object* v_v_891_; lean_object* v_k_892_; lean_object* v_v_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_size_793_);
v_k_890_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_k_890_);
v_v_891_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_v_891_);
lean_dec_ref(v___x_803_);
v_k_892_ = lean_ctor_get(v_l_796_, 1);
v_v_893_ = lean_ctor_get(v_l_796_, 2);
v_isSharedCheck_907_ = !lean_is_exclusive(v_l_796_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; 
v_unused_908_ = lean_ctor_get(v_l_796_, 4);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_l_796_, 3);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_l_796_, 0);
lean_dec(v_unused_910_);
v___x_895_ = v_l_796_;
v_isShared_896_ = v_isSharedCheck_907_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_v_893_);
lean_inc(v_k_892_);
lean_dec(v_l_796_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_907_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_unsigned_to_nat(3u);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_r_797_);
lean_ctor_set(v___x_895_, 3, v_r_797_);
lean_ctor_set(v___x_895_, 2, v_v_891_);
lean_ctor_set(v___x_895_, 1, v_k_890_);
lean_ctor_set(v___x_895_, 0, v___x_798_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_r_797_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_r_797_);
v___x_899_ = v_reuseFailAlloc_906_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 3, v_r_797_);
lean_ctor_set(v___x_877_, 0, v___x_798_);
v___x_901_ = v___x_877_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_r_797_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_797_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v___x_901_);
lean_ctor_set(v___x_801_, 3, v___x_899_);
lean_ctor_set(v___x_801_, 2, v_v_893_);
lean_ctor_set(v___x_801_, 1, v_k_892_);
lean_ctor_set(v___x_801_, 0, v___x_897_);
v___x_903_ = v___x_801_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_892_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_893_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_797_) == 0)
{
lean_object* v_k_911_; lean_object* v_v_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
lean_dec(v_size_793_);
v_k_911_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_k_911_);
v_v_912_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_v_912_);
lean_dec_ref(v___x_803_);
v___x_913_ = lean_unsigned_to_nat(3u);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 4, v_l_796_);
lean_ctor_set(v___x_877_, 2, v_v_912_);
lean_ctor_set(v___x_877_, 1, v_k_911_);
lean_ctor_set(v___x_877_, 0, v___x_798_);
v___x_915_ = v___x_877_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_k_911_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_v_912_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_l_796_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_l_796_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v_r_797_);
lean_ctor_set(v___x_801_, 3, v___x_915_);
lean_ctor_set(v___x_801_, 2, v_v_795_);
lean_ctor_set(v___x_801_, 1, v_k_794_);
lean_ctor_set(v___x_801_, 0, v___x_913_);
v___x_917_ = v___x_801_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_r_797_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v_k_920_; lean_object* v_v_921_; lean_object* v___x_923_; 
v_k_920_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_k_920_);
v_v_921_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_v_921_);
lean_dec_ref(v___x_803_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 3, v_r_797_);
v___x_923_ = v___x_877_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_size_793_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_r_797_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_r_797_);
v___x_923_ = v_reuseFailAlloc_928_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_unsigned_to_nat(2u);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v___x_923_);
lean_ctor_set(v___x_801_, 3, v_r_797_);
lean_ctor_set(v___x_801_, 2, v_v_921_);
lean_ctor_set(v___x_801_, 1, v_k_920_);
lean_ctor_set(v___x_801_, 0, v___x_924_);
v___x_926_ = v___x_801_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_921_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_r_797_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v___x_923_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_r_797_);
lean_inc(v_v_795_);
lean_inc(v_k_794_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1094_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_r_616_, 2);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_r_616_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_1098_);
v___x_942_ = v_r_616_;
v_isShared_943_ = v_isSharedCheck_1093_;
goto v_resetjp_941_;
}
else
{
lean_dec(v_r_616_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_1093_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v_tree_945_; 
v___x_944_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_794_, v_v_795_, v_l_796_, v_r_797_);
v_tree_945_ = lean_ctor_get(v___x_944_, 2);
lean_inc(v_tree_945_);
if (lean_obj_tag(v_tree_945_) == 0)
{
lean_object* v_k_946_; lean_object* v_v_947_; lean_object* v_size_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_k_946_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_k_946_);
v_v_947_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_v_947_);
lean_dec_ref(v___x_944_);
v_size_948_ = lean_ctor_get(v_tree_945_, 0);
v___x_949_ = lean_unsigned_to_nat(3u);
v___x_950_ = lean_nat_mul(v___x_949_, v_size_948_);
v___x_951_ = lean_nat_dec_lt(v___x_950_, v_size_788_);
lean_dec(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec(v_r_792_);
v___x_952_ = lean_nat_add(v___x_798_, v_size_788_);
v___x_953_ = lean_nat_add(v___x_952_, v_size_948_);
lean_dec(v___x_952_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_tree_945_);
lean_ctor_set(v___x_942_, 3, v_l_615_);
lean_ctor_set(v___x_942_, 2, v_v_947_);
lean_ctor_set(v___x_942_, 1, v_k_946_);
lean_ctor_set(v___x_942_, 0, v___x_953_);
v___x_955_ = v___x_942_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_k_946_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_v_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_tree_945_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1022_; 
lean_inc(v_l_791_);
lean_inc(v_v_790_);
lean_inc(v_k_789_);
lean_inc(v_size_788_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1023_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_l_615_, 2);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_l_615_, 1);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_1027_);
v___x_958_ = v_l_615_;
v_isShared_959_ = v_isSharedCheck_1022_;
goto v_resetjp_957_;
}
else
{
lean_dec(v_l_615_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1022_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_size_960_; lean_object* v_size_961_; lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v_l_964_; lean_object* v_r_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_size_960_ = lean_ctor_get(v_l_791_, 0);
v_size_961_ = lean_ctor_get(v_r_792_, 0);
v_k_962_ = lean_ctor_get(v_r_792_, 1);
v_v_963_ = lean_ctor_get(v_r_792_, 2);
v_l_964_ = lean_ctor_get(v_r_792_, 3);
v_r_965_ = lean_ctor_get(v_r_792_, 4);
v___x_966_ = lean_unsigned_to_nat(2u);
v___x_967_ = lean_nat_mul(v___x_966_, v_size_960_);
v___x_968_ = lean_nat_dec_lt(v_size_961_, v___x_967_);
lean_dec(v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1006_; 
lean_inc(v_r_965_);
lean_inc(v_l_964_);
lean_inc(v_v_963_);
lean_inc(v_k_962_);
lean_del_object(v___x_958_);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_r_792_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; 
v_unused_1007_ = lean_ctor_get(v_r_792_, 4);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_r_792_, 3);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_r_792_, 2);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_r_792_, 1);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_r_792_, 0);
lean_dec(v_unused_1011_);
v___x_970_ = v_r_792_;
v_isShared_971_ = v_isSharedCheck_1006_;
goto v_resetjp_969_;
}
else
{
lean_dec(v_r_792_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1006_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___x_994_; lean_object* v___y_996_; 
v___x_972_ = lean_nat_add(v___x_798_, v_size_788_);
lean_dec(v_size_788_);
v___x_973_ = lean_nat_add(v___x_972_, v_size_948_);
lean_dec(v___x_972_);
v___x_994_ = lean_nat_add(v___x_798_, v_size_960_);
if (lean_obj_tag(v_l_964_) == 0)
{
lean_object* v_size_1004_; 
v_size_1004_ = lean_ctor_get(v_l_964_, 0);
lean_inc(v_size_1004_);
v___y_996_ = v_size_1004_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_unsigned_to_nat(0u);
v___y_996_ = v___x_1005_;
goto v___jp_995_;
}
v___jp_974_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_nat_add(v___y_975_, v___y_977_);
lean_dec(v___y_977_);
lean_dec(v___y_975_);
lean_inc_ref(v_tree_945_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 4, v_tree_945_);
lean_ctor_set(v___x_970_, 3, v_r_965_);
lean_ctor_set(v___x_970_, 2, v_v_947_);
lean_ctor_set(v___x_970_, 1, v_k_946_);
lean_ctor_set(v___x_970_, 0, v___x_978_);
v___x_980_ = v___x_970_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_946_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_947_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_r_965_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_tree_945_);
v___x_980_ = v_reuseFailAlloc_993_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_isSharedCheck_987_ = !lean_is_exclusive(v_tree_945_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; 
v_unused_988_ = lean_ctor_get(v_tree_945_, 4);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_tree_945_, 3);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_tree_945_, 2);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_tree_945_, 1);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_tree_945_, 0);
lean_dec(v_unused_992_);
v___x_982_ = v_tree_945_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_tree_945_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v___x_980_);
lean_ctor_set(v___x_982_, 3, v___y_976_);
lean_ctor_set(v___x_982_, 2, v_v_963_);
lean_ctor_set(v___x_982_, 1, v_k_962_);
lean_ctor_set(v___x_982_, 0, v___x_973_);
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_k_962_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_v_963_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v___y_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v___x_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_nat_add(v___x_994_, v___y_996_);
lean_dec(v___y_996_);
lean_dec(v___x_994_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_l_964_);
lean_ctor_set(v___x_942_, 3, v_l_791_);
lean_ctor_set(v___x_942_, 2, v_v_790_);
lean_ctor_set(v___x_942_, 1, v_k_789_);
lean_ctor_set(v___x_942_, 0, v___x_997_);
v___x_999_ = v___x_942_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_k_789_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_v_790_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_l_791_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_l_964_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_nat_add(v___x_798_, v_size_948_);
if (lean_obj_tag(v_r_965_) == 0)
{
lean_object* v_size_1001_; 
v_size_1001_ = lean_ctor_get(v_r_965_, 0);
lean_inc(v_size_1001_);
v___y_975_ = v___x_1000_;
v___y_976_ = v___x_999_;
v___y_977_ = v_size_1001_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___y_975_ = v___x_1000_;
v___y_976_ = v___x_999_;
v___y_977_ = v___x_1002_;
goto v___jp_974_;
}
}
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1012_ = lean_nat_add(v___x_798_, v_size_788_);
lean_dec(v_size_788_);
v___x_1013_ = lean_nat_add(v___x_1012_, v_size_948_);
lean_dec(v___x_1012_);
v___x_1014_ = lean_nat_add(v___x_798_, v_size_948_);
v___x_1015_ = lean_nat_add(v___x_1014_, v_size_961_);
lean_dec(v___x_1014_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_tree_945_);
lean_ctor_set(v___x_942_, 3, v_r_792_);
lean_ctor_set(v___x_942_, 2, v_v_947_);
lean_ctor_set(v___x_942_, 1, v_k_946_);
lean_ctor_set(v___x_942_, 0, v___x_1015_);
v___x_1017_ = v___x_942_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_k_946_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_v_947_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_r_792_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_tree_945_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 4, v___x_1017_);
lean_ctor_set(v___x_958_, 0, v___x_1013_);
v___x_1019_ = v___x_958_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_789_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_790_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_l_791_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_791_) == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1051_; 
lean_inc_ref(v_l_791_);
lean_inc(v_v_790_);
lean_inc(v_k_789_);
lean_inc(v_size_788_);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; lean_object* v_unused_1053_; lean_object* v_unused_1054_; lean_object* v_unused_1055_; lean_object* v_unused_1056_; 
v_unused_1052_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_l_615_, 2);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_l_615_, 1);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_1056_);
v___x_1029_ = v_l_615_;
v_isShared_1030_ = v_isSharedCheck_1051_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v_l_615_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1051_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
if (lean_obj_tag(v_r_792_) == 0)
{
lean_object* v_k_1031_; lean_object* v_v_1032_; lean_object* v_size_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v_k_1031_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_k_1031_);
v_v_1032_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_v_1032_);
lean_dec_ref(v___x_944_);
v_size_1033_ = lean_ctor_get(v_r_792_, 0);
v___x_1034_ = lean_nat_add(v___x_798_, v_size_788_);
lean_dec(v_size_788_);
v___x_1035_ = lean_nat_add(v___x_798_, v_size_1033_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_tree_945_);
lean_ctor_set(v___x_942_, 3, v_r_792_);
lean_ctor_set(v___x_942_, 2, v_v_1032_);
lean_ctor_set(v___x_942_, 1, v_k_1031_);
lean_ctor_set(v___x_942_, 0, v___x_1035_);
v___x_1037_ = v___x_942_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_r_792_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_tree_945_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v___x_1037_);
lean_ctor_set(v___x_1029_, 0, v___x_1034_);
v___x_1039_ = v___x_1029_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_789_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_790_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_l_791_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v_k_1042_; lean_object* v_v_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec(v_size_788_);
v_k_1042_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_k_1042_);
v_v_1043_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_v_1043_);
lean_dec_ref(v___x_944_);
v___x_1044_ = lean_unsigned_to_nat(3u);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_r_792_);
lean_ctor_set(v___x_942_, 3, v_r_792_);
lean_ctor_set(v___x_942_, 2, v_v_1043_);
lean_ctor_set(v___x_942_, 1, v_k_1042_);
lean_ctor_set(v___x_942_, 0, v___x_798_);
v___x_1046_ = v___x_942_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_r_792_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_r_792_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v___x_1046_);
lean_ctor_set(v___x_1029_, 0, v___x_1044_);
v___x_1048_ = v___x_1029_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_789_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_790_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_l_791_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_792_) == 0)
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1081_; 
lean_inc(v_l_791_);
lean_inc(v_v_790_);
lean_inc(v_k_789_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; lean_object* v_unused_1086_; 
v_unused_1082_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_615_, 2);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_l_615_, 1);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_1086_);
v___x_1058_ = v_l_615_;
v_isShared_1059_ = v_isSharedCheck_1081_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v_l_615_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1081_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_k_1060_; lean_object* v_v_1061_; lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1077_; 
v_k_1060_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_k_1060_);
v_v_1061_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_v_1061_);
lean_dec_ref(v___x_944_);
v_k_1062_ = lean_ctor_get(v_r_792_, 1);
v_v_1063_ = lean_ctor_get(v_r_792_, 2);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_r_792_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; lean_object* v_unused_1079_; lean_object* v_unused_1080_; 
v_unused_1078_ = lean_ctor_get(v_r_792_, 4);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_r_792_, 3);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_r_792_, 0);
lean_dec(v_unused_1080_);
v___x_1065_ = v_r_792_;
v_isShared_1066_ = v_isSharedCheck_1077_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_v_1063_);
lean_inc(v_k_1062_);
lean_dec(v_r_792_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1077_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_unsigned_to_nat(3u);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_l_791_);
lean_ctor_set(v___x_1065_, 3, v_l_791_);
lean_ctor_set(v___x_1065_, 2, v_v_790_);
lean_ctor_set(v___x_1065_, 1, v_k_789_);
lean_ctor_set(v___x_1065_, 0, v___x_798_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_789_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_790_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_l_791_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_l_791_);
v___x_1069_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_l_791_);
lean_ctor_set(v___x_942_, 3, v_l_791_);
lean_ctor_set(v___x_942_, 2, v_v_1061_);
lean_ctor_set(v___x_942_, 1, v_k_1060_);
lean_ctor_set(v___x_942_, 0, v___x_798_);
v___x_1071_ = v___x_942_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_l_791_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_l_791_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___x_1071_);
lean_ctor_set(v___x_1058_, 3, v___x_1069_);
lean_ctor_set(v___x_1058_, 2, v_v_1063_);
lean_ctor_set(v___x_1058_, 1, v_k_1062_);
lean_ctor_set(v___x_1058_, 0, v___x_1067_);
v___x_1073_ = v___x_1058_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_1062_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
else
{
lean_object* v_k_1087_; lean_object* v_v_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_k_1087_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_k_1087_);
v_v_1088_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_v_1088_);
lean_dec_ref(v___x_944_);
v___x_1089_ = lean_unsigned_to_nat(2u);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_r_792_);
lean_ctor_set(v___x_942_, 3, v_l_615_);
lean_ctor_set(v___x_942_, 2, v_v_1088_);
lean_ctor_set(v___x_942_, 1, v_k_1087_);
lean_ctor_set(v___x_942_, 0, v___x_1089_);
v___x_1091_ = v___x_942_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_r_792_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
}
else
{
return v_l_615_;
}
}
else
{
return v_r_616_;
}
}
}
else
{
lean_object* v_impl_1099_; lean_object* v___x_1100_; 
v_impl_1099_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_611_, v_l_615_);
v___x_1100_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1099_) == 0)
{
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_size_1101_; lean_object* v_size_1102_; lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v_l_1105_; lean_object* v_r_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_size_1101_ = lean_ctor_get(v_impl_1099_, 0);
lean_inc(v_size_1101_);
v_size_1102_ = lean_ctor_get(v_r_616_, 0);
v_k_1103_ = lean_ctor_get(v_r_616_, 1);
v_v_1104_ = lean_ctor_get(v_r_616_, 2);
v_l_1105_ = lean_ctor_get(v_r_616_, 3);
lean_inc(v_l_1105_);
v_r_1106_ = lean_ctor_get(v_r_616_, 4);
v___x_1107_ = lean_unsigned_to_nat(3u);
v___x_1108_ = lean_nat_mul(v___x_1107_, v_size_1101_);
v___x_1109_ = lean_nat_dec_lt(v___x_1108_, v_size_1102_);
lean_dec(v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_l_1105_);
v___x_1110_ = lean_nat_add(v___x_1100_, v_size_1101_);
lean_dec(v_size_1101_);
v___x_1111_ = lean_nat_add(v___x_1110_, v_size_1102_);
lean_dec(v___x_1110_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 3, v_impl_1099_);
lean_ctor_set(v___x_618_, 0, v___x_1111_);
v___x_1113_ = v___x_618_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_r_616_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1178_; 
lean_inc(v_r_1106_);
lean_inc(v_v_1104_);
lean_inc(v_k_1103_);
lean_inc(v_size_1102_);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1179_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_r_616_, 2);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_r_616_, 1);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_1183_);
v___x_1116_ = v_r_616_;
v_isShared_1117_ = v_isSharedCheck_1178_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_r_616_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1178_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_size_1118_; lean_object* v_k_1119_; lean_object* v_v_1120_; lean_object* v_l_1121_; lean_object* v_r_1122_; lean_object* v_size_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_size_1118_ = lean_ctor_get(v_l_1105_, 0);
v_k_1119_ = lean_ctor_get(v_l_1105_, 1);
v_v_1120_ = lean_ctor_get(v_l_1105_, 2);
v_l_1121_ = lean_ctor_get(v_l_1105_, 3);
v_r_1122_ = lean_ctor_get(v_l_1105_, 4);
v_size_1123_ = lean_ctor_get(v_r_1106_, 0);
v___x_1124_ = lean_unsigned_to_nat(2u);
v___x_1125_ = lean_nat_mul(v___x_1124_, v_size_1123_);
v___x_1126_ = lean_nat_dec_lt(v_size_1118_, v___x_1125_);
lean_dec(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1154_; 
lean_inc(v_r_1122_);
lean_inc(v_l_1121_);
lean_inc(v_v_1120_);
lean_inc(v_k_1119_);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1155_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_l_1105_, 2);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_l_1105_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1159_);
v___x_1128_ = v_l_1105_;
v_isShared_1129_ = v_isSharedCheck_1154_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v_l_1105_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1154_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1144_; 
v___x_1130_ = lean_nat_add(v___x_1100_, v_size_1101_);
lean_dec(v_size_1101_);
v___x_1131_ = lean_nat_add(v___x_1130_, v_size_1102_);
lean_dec(v_size_1102_);
if (lean_obj_tag(v_l_1121_) == 0)
{
lean_object* v_size_1152_; 
v_size_1152_ = lean_ctor_get(v_l_1121_, 0);
lean_inc(v_size_1152_);
v___y_1144_ = v_size_1152_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v___y_1144_ = v___x_1153_;
goto v___jp_1143_;
}
v___jp_1132_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_nat_add(v___y_1133_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec(v___y_1133_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v_r_1106_);
lean_ctor_set(v___x_1128_, 3, v_r_1122_);
lean_ctor_set(v___x_1128_, 2, v_v_1104_);
lean_ctor_set(v___x_1128_, 1, v_k_1103_);
lean_ctor_set(v___x_1128_, 0, v___x_1136_);
v___x_1138_ = v___x_1128_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_r_1122_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_r_1106_);
v___x_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v___x_1138_);
lean_ctor_set(v___x_1116_, 3, v___y_1134_);
lean_ctor_set(v___x_1116_, 2, v_v_1120_);
lean_ctor_set(v___x_1116_, 1, v_k_1119_);
lean_ctor_set(v___x_1116_, 0, v___x_1131_);
v___x_1140_ = v___x_1116_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_1119_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_1120_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v___y_1134_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
v___jp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_nat_add(v___x_1130_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec(v___x_1130_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_l_1121_);
lean_ctor_set(v___x_618_, 3, v_impl_1099_);
lean_ctor_set(v___x_618_, 0, v___x_1145_);
v___x_1147_ = v___x_618_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_l_1121_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_nat_add(v___x_1100_, v_size_1123_);
if (lean_obj_tag(v_r_1122_) == 0)
{
lean_object* v_size_1149_; 
v_size_1149_ = lean_ctor_get(v_r_1122_, 0);
lean_inc(v_size_1149_);
v___y_1133_ = v___x_1148_;
v___y_1134_ = v___x_1147_;
v___y_1135_ = v_size_1149_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___y_1133_ = v___x_1148_;
v___y_1134_ = v___x_1147_;
v___y_1135_ = v___x_1150_;
goto v___jp_1132_;
}
}
}
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_del_object(v___x_618_);
v___x_1160_ = lean_nat_add(v___x_1100_, v_size_1101_);
lean_dec(v_size_1101_);
v___x_1161_ = lean_nat_add(v___x_1160_, v_size_1102_);
lean_dec(v_size_1102_);
v___x_1162_ = lean_nat_add(v___x_1160_, v_size_1118_);
lean_dec(v___x_1160_);
lean_inc_ref(v_impl_1099_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v_l_1105_);
lean_ctor_set(v___x_1116_, 3, v_impl_1099_);
lean_ctor_set(v___x_1116_, 2, v_v_614_);
lean_ctor_set(v___x_1116_, 1, v_k_613_);
lean_ctor_set(v___x_1116_, 0, v___x_1162_);
v___x_1164_ = v___x_1116_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_l_1105_);
v___x_1164_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_isSharedCheck_1171_ = !lean_is_exclusive(v_impl_1099_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1172_ = lean_ctor_get(v_impl_1099_, 4);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_impl_1099_, 3);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_impl_1099_, 2);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1099_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1099_, 0);
lean_dec(v_unused_1176_);
v___x_1166_ = v_impl_1099_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_dec(v_impl_1099_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 4, v_r_1106_);
lean_ctor_set(v___x_1166_, 3, v___x_1164_);
lean_ctor_set(v___x_1166_, 2, v_v_1104_);
lean_ctor_set(v___x_1166_, 1, v_k_1103_);
lean_ctor_set(v___x_1166_, 0, v___x_1161_);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_r_1106_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v_size_1184_ = lean_ctor_get(v_impl_1099_, 0);
lean_inc(v_size_1184_);
v___x_1185_ = lean_nat_add(v___x_1100_, v_size_1184_);
lean_dec(v_size_1184_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 3, v_impl_1099_);
lean_ctor_set(v___x_618_, 0, v___x_1185_);
v___x_1187_ = v___x_618_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_r_616_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_l_1189_; 
v_l_1189_ = lean_ctor_get(v_r_616_, 3);
lean_inc(v_l_1189_);
if (lean_obj_tag(v_l_1189_) == 0)
{
lean_object* v_r_1190_; 
v_r_1190_ = lean_ctor_get(v_r_616_, 4);
lean_inc(v_r_1190_);
if (lean_obj_tag(v_r_1190_) == 0)
{
lean_object* v_size_1191_; lean_object* v_k_1192_; lean_object* v_v_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1206_; 
v_size_1191_ = lean_ctor_get(v_r_616_, 0);
v_k_1192_ = lean_ctor_get(v_r_616_, 1);
v_v_1193_ = lean_ctor_get(v_r_616_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1207_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_1208_);
v___x_1195_ = v_r_616_;
v_isShared_1196_ = v_isSharedCheck_1206_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_v_1193_);
lean_inc(v_k_1192_);
lean_inc(v_size_1191_);
lean_dec(v_r_616_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1206_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_size_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v_size_1197_ = lean_ctor_get(v_l_1189_, 0);
v___x_1198_ = lean_nat_add(v___x_1100_, v_size_1191_);
lean_dec(v_size_1191_);
v___x_1199_ = lean_nat_add(v___x_1100_, v_size_1197_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 4, v_l_1189_);
lean_ctor_set(v___x_1195_, 3, v_impl_1099_);
lean_ctor_set(v___x_1195_, 2, v_v_614_);
lean_ctor_set(v___x_1195_, 1, v_k_613_);
lean_ctor_set(v___x_1195_, 0, v___x_1199_);
v___x_1201_ = v___x_1195_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_l_1189_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_r_1190_);
lean_ctor_set(v___x_618_, 3, v___x_1201_);
lean_ctor_set(v___x_618_, 2, v_v_1193_);
lean_ctor_set(v___x_618_, 1, v_k_1192_);
lean_ctor_set(v___x_618_, 0, v___x_1198_);
v___x_1203_ = v___x_618_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1193_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_r_1190_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_k_1209_; lean_object* v_v_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1233_; 
v_k_1209_ = lean_ctor_get(v_r_616_, 1);
v_v_1210_ = lean_ctor_get(v_r_616_, 2);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; 
v_unused_1234_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_1236_);
v___x_1212_ = v_r_616_;
v_isShared_1213_ = v_isSharedCheck_1233_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_v_1210_);
lean_inc(v_k_1209_);
lean_dec(v_r_616_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1233_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_k_1214_; lean_object* v_v_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1229_; 
v_k_1214_ = lean_ctor_get(v_l_1189_, 1);
v_v_1215_ = lean_ctor_get(v_l_1189_, 2);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_l_1189_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1230_ = lean_ctor_get(v_l_1189_, 4);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_l_1189_, 3);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_l_1189_, 0);
lean_dec(v_unused_1232_);
v___x_1217_ = v_l_1189_;
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_dec(v_l_1189_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(3u);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 4, v_r_1190_);
lean_ctor_set(v___x_1217_, 3, v_r_1190_);
lean_ctor_set(v___x_1217_, 2, v_v_614_);
lean_ctor_set(v___x_1217_, 1, v_k_613_);
lean_ctor_set(v___x_1217_, 0, v___x_1100_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_r_1190_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1190_);
v___x_1221_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 3, v_r_1190_);
lean_ctor_set(v___x_1212_, 0, v___x_1100_);
v___x_1223_ = v___x_1212_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_k_1209_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_v_1210_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_r_1190_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_r_1190_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_1223_);
lean_ctor_set(v___x_618_, 3, v___x_1221_);
lean_ctor_set(v___x_618_, 2, v_v_1215_);
lean_ctor_set(v___x_618_, 1, v_k_1214_);
lean_ctor_set(v___x_618_, 0, v___x_1219_);
v___x_1225_ = v___x_618_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1237_; 
v_r_1237_ = lean_ctor_get(v_r_616_, 4);
lean_inc(v_r_1237_);
if (lean_obj_tag(v_r_1237_) == 0)
{
lean_object* v_k_1238_; lean_object* v_v_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1250_; 
v_k_1238_ = lean_ctor_get(v_r_616_, 1);
v_v_1239_ = lean_ctor_get(v_r_616_, 2);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; lean_object* v_unused_1252_; lean_object* v_unused_1253_; 
v_unused_1251_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_1253_);
v___x_1241_ = v_r_616_;
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_v_1239_);
lean_inc(v_k_1238_);
lean_dec(v_r_616_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(3u);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 4, v_l_1189_);
lean_ctor_set(v___x_1241_, 2, v_v_614_);
lean_ctor_set(v___x_1241_, 1, v_k_613_);
lean_ctor_set(v___x_1241_, 0, v___x_1100_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_l_1189_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_l_1189_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_r_1237_);
lean_ctor_set(v___x_618_, 3, v___x_1245_);
lean_ctor_set(v___x_618_, 2, v_v_1239_);
lean_ctor_set(v___x_618_, 1, v_k_1238_);
lean_ctor_set(v___x_618_, 0, v___x_1243_);
v___x_1247_ = v___x_618_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_r_1237_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_size_1254_; lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1267_; 
v_size_1254_ = lean_ctor_get(v_r_616_, 0);
v_k_1255_ = lean_ctor_get(v_r_616_, 1);
v_v_1256_ = lean_ctor_get(v_r_616_, 2);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; lean_object* v_unused_1269_; 
v_unused_1268_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_1268_);
v_unused_1269_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_1269_);
v___x_1258_ = v_r_616_;
v_isShared_1259_ = v_isSharedCheck_1267_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
lean_inc(v_size_1254_);
lean_dec(v_r_616_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1267_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 3, v_r_1237_);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_size_1254_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v_r_1237_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_r_1237_);
v___x_1261_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(2u);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_1261_);
lean_ctor_set(v___x_618_, 3, v_r_1237_);
lean_ctor_set(v___x_618_, 0, v___x_1262_);
v___x_1264_ = v___x_618_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_r_1237_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v___x_1261_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
else
{
lean_object* v___x_1271_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 3, v_r_616_);
lean_ctor_set(v___x_618_, 0, v___x_1100_);
v___x_1271_ = v___x_618_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_r_616_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_r_616_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
else
{
return v_t_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg___boxed(lean_object* v_k_1275_, lean_object* v_t_1276_){
_start:
{
uint64_t v_k_boxed_1277_; lean_object* v_res_1278_; 
v_k_boxed_1277_ = lean_unbox_uint64(v_k_1275_);
lean_dec_ref(v_k_1275_);
v_res_1278_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_boxed_1277_, v_t_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t v_h_1279_, lean_object* v_st_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_h_1279_, v_st_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object* v_h_1282_, lean_object* v_st_1283_){
_start:
{
uint64_t v_h_boxed_1284_; lean_object* v_res_1285_; 
v_h_boxed_1284_ = lean_unbox_uint64(v_h_1282_);
lean_dec_ref(v_h_1282_);
v_res_1285_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_1284_, v_st_1283_);
return v_res_1285_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1292_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_ctor_set(v___x_1292_, 2, v___x_1291_);
lean_ctor_set(v___x_1292_, 3, v___x_1291_);
lean_ctor_set(v___x_1292_, 4, v___x_1291_);
lean_ctor_set(v___x_1292_, 5, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v_env_1300_; lean_object* v_nextMacroScope_1301_; lean_object* v_ngen_1302_; lean_object* v_auxDeclNGen_1303_; lean_object* v_traceState_1304_; lean_object* v_messages_1305_; lean_object* v_infoState_1306_; lean_object* v_snapshotTasks_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1335_; 
v___x_1297_ = lean_box_uint64(v_h_1293_);
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1298_, 0, v___x_1297_);
v___x_1299_ = lean_st_ref_take(v___y_1295_);
v_env_1300_ = lean_ctor_get(v___x_1299_, 0);
v_nextMacroScope_1301_ = lean_ctor_get(v___x_1299_, 1);
v_ngen_1302_ = lean_ctor_get(v___x_1299_, 2);
v_auxDeclNGen_1303_ = lean_ctor_get(v___x_1299_, 3);
v_traceState_1304_ = lean_ctor_get(v___x_1299_, 4);
v_messages_1305_ = lean_ctor_get(v___x_1299_, 6);
v_infoState_1306_ = lean_ctor_get(v___x_1299_, 7);
v_snapshotTasks_1307_ = lean_ctor_get(v___x_1299_, 8);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1299_, 5);
lean_dec(v_unused_1336_);
v___x_1309_ = v___x_1299_;
v_isShared_1310_ = v_isSharedCheck_1335_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_snapshotTasks_1307_);
lean_inc(v_infoState_1306_);
lean_inc(v_messages_1305_);
lean_inc(v_traceState_1304_);
lean_inc(v_auxDeclNGen_1303_);
lean_inc(v_ngen_1302_);
lean_inc(v_nextMacroScope_1301_);
lean_inc(v_env_1300_);
lean_dec(v___x_1299_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1335_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1311_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1312_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1311_, v_env_1300_, v___f_1298_);
v___x_1313_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 5, v___x_1313_);
lean_ctor_set(v___x_1309_, 0, v___x_1312_);
v___x_1315_ = v___x_1309_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_nextMacroScope_1301_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_ngen_1302_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_auxDeclNGen_1303_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_traceState_1304_);
lean_ctor_set(v_reuseFailAlloc_1334_, 5, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1334_, 6, v_messages_1305_);
lean_ctor_set(v_reuseFailAlloc_1334_, 7, v_infoState_1306_);
lean_ctor_set(v_reuseFailAlloc_1334_, 8, v_snapshotTasks_1307_);
v___x_1315_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_mctx_1318_; lean_object* v_zetaDeltaFVarIds_1319_; lean_object* v_postponed_1320_; lean_object* v_diag_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1332_; 
v___x_1316_ = lean_st_ref_put(v___y_1295_, v___x_1315_);
v___x_1317_ = lean_st_ref_take(v___y_1294_);
v_mctx_1318_ = lean_ctor_get(v___x_1317_, 0);
v_zetaDeltaFVarIds_1319_ = lean_ctor_get(v___x_1317_, 2);
v_postponed_1320_ = lean_ctor_get(v___x_1317_, 3);
v_diag_1321_ = lean_ctor_get(v___x_1317_, 4);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1317_, 1);
lean_dec(v_unused_1333_);
v___x_1323_ = v___x_1317_;
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_diag_1321_);
lean_inc(v_postponed_1320_);
lean_inc(v_zetaDeltaFVarIds_1319_);
lean_inc(v_mctx_1318_);
lean_dec(v___x_1317_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_mctx_1318_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_zetaDeltaFVarIds_1319_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_postponed_1320_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_diag_1321_);
v___x_1328_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_st_ref_put(v___y_1294_, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1325_);
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint64_t v_h_boxed_1341_; lean_object* v_res_1342_; 
v_h_boxed_1341_ = lean_unbox_uint64(v_h_1337_);
lean_dec_ref(v_h_1337_);
v_res_1342_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1341_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1343_, uint64_t v_k_1344_, lean_object* v_fallback_1345_){
_start:
{
if (lean_obj_tag(v_t_1343_) == 0)
{
lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v_l_1348_; lean_object* v_r_1349_; uint64_t v___x_1350_; uint8_t v___x_1351_; 
v_k_1346_ = lean_ctor_get(v_t_1343_, 1);
v_v_1347_ = lean_ctor_get(v_t_1343_, 2);
v_l_1348_ = lean_ctor_get(v_t_1343_, 3);
v_r_1349_ = lean_ctor_get(v_t_1343_, 4);
v___x_1350_ = lean_unbox_uint64(v_k_1346_);
v___x_1351_ = lean_uint64_dec_lt(v_k_1344_, v___x_1350_);
if (v___x_1351_ == 0)
{
uint64_t v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_unbox_uint64(v_k_1346_);
v___x_1353_ = lean_uint64_dec_eq(v_k_1344_, v___x_1352_);
if (v___x_1353_ == 0)
{
v_t_1343_ = v_r_1349_;
goto _start;
}
else
{
lean_inc(v_v_1347_);
return v_v_1347_;
}
}
else
{
v_t_1343_ = v_l_1348_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1345_);
return v_fallback_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1356_, lean_object* v_k_1357_, lean_object* v_fallback_1358_){
_start:
{
uint64_t v_k_boxed_1359_; lean_object* v_res_1360_; 
v_k_boxed_1359_ = lean_unbox_uint64(v_k_1357_);
lean_dec_ref(v_k_1357_);
v_res_1360_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1356_, v_k_boxed_1359_, v_fallback_1358_);
lean_dec(v_fallback_1358_);
lean_dec(v_t_1356_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1361_, lean_object* v_v_1362_, lean_object* v_t_1363_){
_start:
{
if (lean_obj_tag(v_t_1363_) == 0)
{
lean_object* v_size_1364_; lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v_l_1367_; lean_object* v_r_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1652_; 
v_size_1364_ = lean_ctor_get(v_t_1363_, 0);
v_k_1365_ = lean_ctor_get(v_t_1363_, 1);
v_v_1366_ = lean_ctor_get(v_t_1363_, 2);
v_l_1367_ = lean_ctor_get(v_t_1363_, 3);
v_r_1368_ = lean_ctor_get(v_t_1363_, 4);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_t_1363_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1370_ = v_t_1363_;
v_isShared_1371_ = v_isSharedCheck_1652_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_r_1368_);
lean_inc(v_l_1367_);
lean_inc(v_v_1366_);
lean_inc(v_k_1365_);
lean_inc(v_size_1364_);
lean_dec(v_t_1363_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1652_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint64_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_unbox_uint64(v_k_1365_);
v___x_1373_ = lean_uint64_dec_lt(v_k_1361_, v___x_1372_);
if (v___x_1373_ == 0)
{
uint64_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_unbox_uint64(v_k_1365_);
v___x_1375_ = lean_uint64_dec_eq(v_k_1361_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v_impl_1376_; lean_object* v___x_1377_; 
lean_dec(v_size_1364_);
v_impl_1376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1361_, v_v_1362_, v_r_1368_);
v___x_1377_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1367_) == 0)
{
lean_object* v_size_1378_; lean_object* v_size_1379_; lean_object* v_k_1380_; lean_object* v_v_1381_; lean_object* v_l_1382_; lean_object* v_r_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_size_1378_ = lean_ctor_get(v_l_1367_, 0);
v_size_1379_ = lean_ctor_get(v_impl_1376_, 0);
lean_inc(v_size_1379_);
v_k_1380_ = lean_ctor_get(v_impl_1376_, 1);
lean_inc(v_k_1380_);
v_v_1381_ = lean_ctor_get(v_impl_1376_, 2);
lean_inc(v_v_1381_);
v_l_1382_ = lean_ctor_get(v_impl_1376_, 3);
lean_inc(v_l_1382_);
v_r_1383_ = lean_ctor_get(v_impl_1376_, 4);
lean_inc(v_r_1383_);
v___x_1384_ = lean_unsigned_to_nat(3u);
v___x_1385_ = lean_nat_mul(v___x_1384_, v_size_1378_);
v___x_1386_ = lean_nat_dec_lt(v___x_1385_, v_size_1379_);
lean_dec(v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec(v_r_1383_);
lean_dec(v_l_1382_);
lean_dec(v_v_1381_);
lean_dec(v_k_1380_);
v___x_1387_ = lean_nat_add(v___x_1377_, v_size_1378_);
v___x_1388_ = lean_nat_add(v___x_1387_, v_size_1379_);
lean_dec(v_size_1379_);
lean_dec(v___x_1387_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_impl_1376_);
lean_ctor_set(v___x_1370_, 0, v___x_1388_);
v___x_1390_ = v___x_1370_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_l_1367_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_impl_1376_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1455_; 
v_isSharedCheck_1455_ = !lean_is_exclusive(v_impl_1376_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1456_ = lean_ctor_get(v_impl_1376_, 4);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_impl_1376_, 3);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_impl_1376_, 2);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_impl_1376_, 1);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_impl_1376_, 0);
lean_dec(v_unused_1460_);
v___x_1393_ = v_impl_1376_;
v_isShared_1394_ = v_isSharedCheck_1455_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_impl_1376_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1455_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_l_1398_; lean_object* v_r_1399_; lean_object* v_size_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_size_1395_ = lean_ctor_get(v_l_1382_, 0);
v_k_1396_ = lean_ctor_get(v_l_1382_, 1);
v_v_1397_ = lean_ctor_get(v_l_1382_, 2);
v_l_1398_ = lean_ctor_get(v_l_1382_, 3);
v_r_1399_ = lean_ctor_get(v_l_1382_, 4);
v_size_1400_ = lean_ctor_get(v_r_1383_, 0);
v___x_1401_ = lean_unsigned_to_nat(2u);
v___x_1402_ = lean_nat_mul(v___x_1401_, v_size_1400_);
v___x_1403_ = lean_nat_dec_lt(v_size_1395_, v___x_1402_);
lean_dec(v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1431_; 
lean_inc(v_r_1399_);
lean_inc(v_l_1398_);
lean_inc(v_v_1397_);
lean_inc(v_k_1396_);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_l_1382_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; 
v_unused_1432_ = lean_ctor_get(v_l_1382_, 4);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_l_1382_, 3);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_l_1382_, 2);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_l_1382_, 1);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_l_1382_, 0);
lean_dec(v_unused_1436_);
v___x_1405_ = v_l_1382_;
v_isShared_1406_ = v_isSharedCheck_1431_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_l_1382_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1431_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1421_; 
v___x_1407_ = lean_nat_add(v___x_1377_, v_size_1378_);
v___x_1408_ = lean_nat_add(v___x_1407_, v_size_1379_);
lean_dec(v_size_1379_);
if (lean_obj_tag(v_l_1398_) == 0)
{
lean_object* v_size_1429_; 
v_size_1429_ = lean_ctor_get(v_l_1398_, 0);
lean_inc(v_size_1429_);
v___y_1421_ = v_size_1429_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1421_ = v___x_1430_;
goto v___jp_1420_;
}
v___jp_1409_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_nat_add(v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec(v___y_1411_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 4, v_r_1383_);
lean_ctor_set(v___x_1405_, 3, v_r_1399_);
lean_ctor_set(v___x_1405_, 2, v_v_1381_);
lean_ctor_set(v___x_1405_, 1, v_k_1380_);
lean_ctor_set(v___x_1405_, 0, v___x_1413_);
v___x_1415_ = v___x_1405_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_r_1399_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_r_1383_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v___x_1415_);
lean_ctor_set(v___x_1393_, 3, v___y_1410_);
lean_ctor_set(v___x_1393_, 2, v_v_1397_);
lean_ctor_set(v___x_1393_, 1, v_k_1396_);
lean_ctor_set(v___x_1393_, 0, v___x_1408_);
v___x_1417_ = v___x_1393_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v___y_1410_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
v___jp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_nat_add(v___x_1407_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec(v___x_1407_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_l_1398_);
lean_ctor_set(v___x_1370_, 0, v___x_1422_);
v___x_1424_ = v___x_1370_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_l_1367_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_l_1398_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_nat_add(v___x_1377_, v_size_1400_);
if (lean_obj_tag(v_r_1399_) == 0)
{
lean_object* v_size_1426_; 
v_size_1426_ = lean_ctor_get(v_r_1399_, 0);
lean_inc(v_size_1426_);
v___y_1410_ = v___x_1424_;
v___y_1411_ = v___x_1425_;
v___y_1412_ = v_size_1426_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___y_1410_ = v___x_1424_;
v___y_1411_ = v___x_1425_;
v___y_1412_ = v___x_1427_;
goto v___jp_1409_;
}
}
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_del_object(v___x_1370_);
v___x_1437_ = lean_nat_add(v___x_1377_, v_size_1378_);
v___x_1438_ = lean_nat_add(v___x_1437_, v_size_1379_);
lean_dec(v_size_1379_);
v___x_1439_ = lean_nat_add(v___x_1437_, v_size_1395_);
lean_dec(v___x_1437_);
lean_inc_ref(v_l_1367_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_l_1382_);
lean_ctor_set(v___x_1393_, 3, v_l_1367_);
lean_ctor_set(v___x_1393_, 2, v_v_1366_);
lean_ctor_set(v___x_1393_, 1, v_k_1365_);
lean_ctor_set(v___x_1393_, 0, v___x_1439_);
v___x_1441_ = v___x_1393_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_l_1367_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_l_1382_);
v___x_1441_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v_l_1367_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; 
v_unused_1449_ = lean_ctor_get(v_l_1367_, 4);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_l_1367_, 3);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1367_, 2);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1367_, 1);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_l_1367_, 0);
lean_dec(v_unused_1453_);
v___x_1443_ = v_l_1367_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_l_1367_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_r_1383_);
lean_ctor_set(v___x_1443_, 3, v___x_1441_);
lean_ctor_set(v___x_1443_, 2, v_v_1381_);
lean_ctor_set(v___x_1443_, 1, v_k_1380_);
lean_ctor_set(v___x_1443_, 0, v___x_1438_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_r_1383_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1461_; 
v_l_1461_ = lean_ctor_get(v_impl_1376_, 3);
lean_inc(v_l_1461_);
if (lean_obj_tag(v_l_1461_) == 0)
{
lean_object* v_r_1462_; lean_object* v_k_1463_; lean_object* v_v_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1487_; 
v_r_1462_ = lean_ctor_get(v_impl_1376_, 4);
v_k_1463_ = lean_ctor_get(v_impl_1376_, 1);
v_v_1464_ = lean_ctor_get(v_impl_1376_, 2);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_impl_1376_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1488_ = lean_ctor_get(v_impl_1376_, 3);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_impl_1376_, 0);
lean_dec(v_unused_1489_);
v___x_1466_ = v_impl_1376_;
v_isShared_1467_ = v_isSharedCheck_1487_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_r_1462_);
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
lean_dec(v_impl_1376_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1487_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1483_; 
v_k_1468_ = lean_ctor_get(v_l_1461_, 1);
v_v_1469_ = lean_ctor_get(v_l_1461_, 2);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_l_1461_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1484_ = lean_ctor_get(v_l_1461_, 4);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_l_1461_, 3);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_l_1461_, 0);
lean_dec(v_unused_1486_);
v___x_1471_ = v_l_1461_;
v_isShared_1472_ = v_isSharedCheck_1483_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
lean_dec(v_l_1461_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1483_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1462_, 2);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v_r_1462_);
lean_ctor_set(v___x_1471_, 3, v_r_1462_);
lean_ctor_set(v___x_1471_, 2, v_v_1366_);
lean_ctor_set(v___x_1471_, 1, v_k_1365_);
lean_ctor_set(v___x_1471_, 0, v___x_1377_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_r_1462_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_r_1462_);
v___x_1475_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
lean_inc(v_r_1462_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 3, v_r_1462_);
lean_ctor_set(v___x_1466_, 0, v___x_1377_);
v___x_1477_ = v___x_1466_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_r_1462_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_r_1462_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v___x_1477_);
lean_ctor_set(v___x_1370_, 3, v___x_1475_);
lean_ctor_set(v___x_1370_, 2, v_v_1469_);
lean_ctor_set(v___x_1370_, 1, v_k_1468_);
lean_ctor_set(v___x_1370_, 0, v___x_1473_);
v___x_1479_ = v___x_1370_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
else
{
lean_object* v_r_1490_; 
v_r_1490_ = lean_ctor_get(v_impl_1376_, 4);
lean_inc(v_r_1490_);
if (lean_obj_tag(v_r_1490_) == 0)
{
lean_object* v_k_1491_; lean_object* v_v_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1503_; 
v_k_1491_ = lean_ctor_get(v_impl_1376_, 1);
v_v_1492_ = lean_ctor_get(v_impl_1376_, 2);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_impl_1376_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; 
v_unused_1504_ = lean_ctor_get(v_impl_1376_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_impl_1376_, 3);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_impl_1376_, 0);
lean_dec(v_unused_1506_);
v___x_1494_ = v_impl_1376_;
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_v_1492_);
lean_inc(v_k_1491_);
lean_dec(v_impl_1376_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_unsigned_to_nat(3u);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 4, v_l_1461_);
lean_ctor_set(v___x_1494_, 2, v_v_1366_);
lean_ctor_set(v___x_1494_, 1, v_k_1365_);
lean_ctor_set(v___x_1494_, 0, v___x_1377_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_l_1461_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1461_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_r_1490_);
lean_ctor_set(v___x_1370_, 3, v___x_1498_);
lean_ctor_set(v___x_1370_, 2, v_v_1492_);
lean_ctor_set(v___x_1370_, 1, v_k_1491_);
lean_ctor_set(v___x_1370_, 0, v___x_1496_);
v___x_1500_ = v___x_1370_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1492_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1490_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_unsigned_to_nat(2u);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_impl_1376_);
lean_ctor_set(v___x_1370_, 3, v_r_1490_);
lean_ctor_set(v___x_1370_, 0, v___x_1507_);
v___x_1509_ = v___x_1370_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_r_1490_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_impl_1376_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_dec(v_v_1366_);
lean_dec(v_k_1365_);
v___x_1511_ = lean_box_uint64(v_k_1361_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 2, v_v_1362_);
lean_ctor_set(v___x_1370_, 1, v___x_1511_);
v___x_1513_ = v___x_1370_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_size_1364_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_l_1367_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1368_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_impl_1515_; lean_object* v___x_1516_; 
lean_dec(v_size_1364_);
v_impl_1515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1361_, v_v_1362_, v_l_1367_);
v___x_1516_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1368_) == 0)
{
lean_object* v_size_1517_; lean_object* v_size_1518_; lean_object* v_k_1519_; lean_object* v_v_1520_; lean_object* v_l_1521_; lean_object* v_r_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_size_1517_ = lean_ctor_get(v_r_1368_, 0);
v_size_1518_ = lean_ctor_get(v_impl_1515_, 0);
lean_inc(v_size_1518_);
v_k_1519_ = lean_ctor_get(v_impl_1515_, 1);
lean_inc(v_k_1519_);
v_v_1520_ = lean_ctor_get(v_impl_1515_, 2);
lean_inc(v_v_1520_);
v_l_1521_ = lean_ctor_get(v_impl_1515_, 3);
lean_inc(v_l_1521_);
v_r_1522_ = lean_ctor_get(v_impl_1515_, 4);
lean_inc(v_r_1522_);
v___x_1523_ = lean_unsigned_to_nat(3u);
v___x_1524_ = lean_nat_mul(v___x_1523_, v_size_1517_);
v___x_1525_ = lean_nat_dec_lt(v___x_1524_, v_size_1518_);
lean_dec(v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_dec(v_r_1522_);
lean_dec(v_l_1521_);
lean_dec(v_v_1520_);
lean_dec(v_k_1519_);
v___x_1526_ = lean_nat_add(v___x_1516_, v_size_1518_);
lean_dec(v_size_1518_);
v___x_1527_ = lean_nat_add(v___x_1526_, v_size_1517_);
lean_dec(v___x_1526_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 3, v_impl_1515_);
lean_ctor_set(v___x_1370_, 0, v___x_1527_);
v___x_1529_ = v___x_1370_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_impl_1515_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1368_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
else
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1596_; 
v_isSharedCheck_1596_ = !lean_is_exclusive(v_impl_1515_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1597_ = lean_ctor_get(v_impl_1515_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1515_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1515_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1515_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1515_, 0);
lean_dec(v_unused_1601_);
v___x_1532_ = v_impl_1515_;
v_isShared_1533_ = v_isSharedCheck_1596_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_impl_1515_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1596_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_size_1534_; lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_l_1538_; lean_object* v_r_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_size_1534_ = lean_ctor_get(v_l_1521_, 0);
v_size_1535_ = lean_ctor_get(v_r_1522_, 0);
v_k_1536_ = lean_ctor_get(v_r_1522_, 1);
v_v_1537_ = lean_ctor_get(v_r_1522_, 2);
v_l_1538_ = lean_ctor_get(v_r_1522_, 3);
v_r_1539_ = lean_ctor_get(v_r_1522_, 4);
v___x_1540_ = lean_unsigned_to_nat(2u);
v___x_1541_ = lean_nat_mul(v___x_1540_, v_size_1534_);
v___x_1542_ = lean_nat_dec_lt(v_size_1535_, v___x_1541_);
lean_dec(v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1571_; 
lean_inc(v_r_1539_);
lean_inc(v_l_1538_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_r_1522_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; 
v_unused_1572_ = lean_ctor_get(v_r_1522_, 4);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_r_1522_, 3);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_r_1522_, 2);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_r_1522_, 1);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_r_1522_, 0);
lean_dec(v_unused_1576_);
v___x_1544_ = v_r_1522_;
v_isShared_1545_ = v_isSharedCheck_1571_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v_r_1522_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1571_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___x_1559_; lean_object* v___y_1561_; 
v___x_1546_ = lean_nat_add(v___x_1516_, v_size_1518_);
lean_dec(v_size_1518_);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1517_);
lean_dec(v___x_1546_);
v___x_1559_ = lean_nat_add(v___x_1516_, v_size_1534_);
if (lean_obj_tag(v_l_1538_) == 0)
{
lean_object* v_size_1569_; 
v_size_1569_ = lean_ctor_get(v_l_1538_, 0);
lean_inc(v_size_1569_);
v___y_1561_ = v_size_1569_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(0u);
v___y_1561_ = v___x_1570_;
goto v___jp_1560_;
}
v___jp_1548_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_nat_add(v___y_1549_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec(v___y_1549_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v_r_1368_);
lean_ctor_set(v___x_1544_, 3, v_r_1539_);
lean_ctor_set(v___x_1544_, 2, v_v_1366_);
lean_ctor_set(v___x_1544_, 1, v_k_1365_);
lean_ctor_set(v___x_1544_, 0, v___x_1552_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1368_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v___x_1554_);
lean_ctor_set(v___x_1532_, 3, v___y_1550_);
lean_ctor_set(v___x_1532_, 2, v_v_1537_);
lean_ctor_set(v___x_1532_, 1, v_k_1536_);
lean_ctor_set(v___x_1532_, 0, v___x_1547_);
v___x_1556_ = v___x_1532_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v___y_1550_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_nat_add(v___x_1559_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec(v___x_1559_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_l_1538_);
lean_ctor_set(v___x_1370_, 3, v_l_1521_);
lean_ctor_set(v___x_1370_, 2, v_v_1520_);
lean_ctor_set(v___x_1370_, 1, v_k_1519_);
lean_ctor_set(v___x_1370_, 0, v___x_1562_);
v___x_1564_ = v___x_1370_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_k_1519_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_v_1520_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v_l_1521_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_l_1538_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_nat_add(v___x_1516_, v_size_1517_);
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_size_1566_; 
v_size_1566_ = lean_ctor_get(v_r_1539_, 0);
lean_inc(v_size_1566_);
v___y_1549_ = v___x_1565_;
v___y_1550_ = v___x_1564_;
v___y_1551_ = v_size_1566_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
v___y_1549_ = v___x_1565_;
v___y_1550_ = v___x_1564_;
v___y_1551_ = v___x_1567_;
goto v___jp_1548_;
}
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_del_object(v___x_1370_);
v___x_1577_ = lean_nat_add(v___x_1516_, v_size_1518_);
lean_dec(v_size_1518_);
v___x_1578_ = lean_nat_add(v___x_1577_, v_size_1517_);
lean_dec(v___x_1577_);
v___x_1579_ = lean_nat_add(v___x_1516_, v_size_1517_);
v___x_1580_ = lean_nat_add(v___x_1579_, v_size_1535_);
lean_dec(v___x_1579_);
lean_inc_ref(v_r_1368_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v_r_1368_);
lean_ctor_set(v___x_1532_, 3, v_r_1522_);
lean_ctor_set(v___x_1532_, 2, v_v_1366_);
lean_ctor_set(v___x_1532_, 1, v_k_1365_);
lean_ctor_set(v___x_1532_, 0, v___x_1580_);
v___x_1582_ = v___x_1532_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_r_1522_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_r_1368_);
v___x_1582_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_isSharedCheck_1589_ = !lean_is_exclusive(v_r_1368_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; 
v_unused_1590_ = lean_ctor_get(v_r_1368_, 4);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_r_1368_, 3);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_r_1368_, 2);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_r_1368_, 1);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_r_1368_, 0);
lean_dec(v_unused_1594_);
v___x_1584_ = v_r_1368_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_r_1368_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v___x_1582_);
lean_ctor_set(v___x_1584_, 3, v_l_1521_);
lean_ctor_set(v___x_1584_, 2, v_v_1520_);
lean_ctor_set(v___x_1584_, 1, v_k_1519_);
lean_ctor_set(v___x_1584_, 0, v___x_1578_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_k_1519_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_v_1520_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_l_1521_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v___x_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1602_; 
v_l_1602_ = lean_ctor_get(v_impl_1515_, 3);
lean_inc(v_l_1602_);
if (lean_obj_tag(v_l_1602_) == 0)
{
lean_object* v_r_1603_; lean_object* v_k_1604_; lean_object* v_v_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1616_; 
v_r_1603_ = lean_ctor_get(v_impl_1515_, 4);
v_k_1604_ = lean_ctor_get(v_impl_1515_, 1);
v_v_1605_ = lean_ctor_get(v_impl_1515_, 2);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_impl_1515_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; 
v_unused_1617_ = lean_ctor_get(v_impl_1515_, 3);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_impl_1515_, 0);
lean_dec(v_unused_1618_);
v___x_1607_ = v_impl_1515_;
v_isShared_1608_ = v_isSharedCheck_1616_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_r_1603_);
lean_inc(v_v_1605_);
lean_inc(v_k_1604_);
lean_dec(v_impl_1515_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1616_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1603_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 3, v_r_1603_);
lean_ctor_set(v___x_1607_, 2, v_v_1366_);
lean_ctor_set(v___x_1607_, 1, v_k_1365_);
lean_ctor_set(v___x_1607_, 0, v___x_1516_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_r_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_r_1603_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v___x_1611_);
lean_ctor_set(v___x_1370_, 3, v_l_1602_);
lean_ctor_set(v___x_1370_, 2, v_v_1605_);
lean_ctor_set(v___x_1370_, 1, v_k_1604_);
lean_ctor_set(v___x_1370_, 0, v___x_1609_);
v___x_1613_ = v___x_1370_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1605_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_l_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_r_1619_; 
v_r_1619_ = lean_ctor_get(v_impl_1515_, 4);
lean_inc(v_r_1619_);
if (lean_obj_tag(v_r_1619_) == 0)
{
lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1644_; 
v_k_1620_ = lean_ctor_get(v_impl_1515_, 1);
v_v_1621_ = lean_ctor_get(v_impl_1515_, 2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_impl_1515_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; 
v_unused_1645_ = lean_ctor_get(v_impl_1515_, 4);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_impl_1515_, 3);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_impl_1515_, 0);
lean_dec(v_unused_1647_);
v___x_1623_ = v_impl_1515_;
v_isShared_1624_ = v_isSharedCheck_1644_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_v_1621_);
lean_inc(v_k_1620_);
lean_dec(v_impl_1515_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1644_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_k_1625_; lean_object* v_v_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1640_; 
v_k_1625_ = lean_ctor_get(v_r_1619_, 1);
v_v_1626_ = lean_ctor_get(v_r_1619_, 2);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_r_1619_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; 
v_unused_1641_ = lean_ctor_get(v_r_1619_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_r_1619_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_r_1619_, 0);
lean_dec(v_unused_1643_);
v___x_1628_ = v_r_1619_;
v_isShared_1629_ = v_isSharedCheck_1640_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_v_1626_);
lean_inc(v_k_1625_);
lean_dec(v_r_1619_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1640_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = lean_unsigned_to_nat(3u);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 4, v_l_1602_);
lean_ctor_set(v___x_1628_, 3, v_l_1602_);
lean_ctor_set(v___x_1628_, 2, v_v_1621_);
lean_ctor_set(v___x_1628_, 1, v_k_1620_);
lean_ctor_set(v___x_1628_, 0, v___x_1516_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_l_1602_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_l_1602_);
v___x_1632_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1634_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_l_1602_);
lean_ctor_set(v___x_1623_, 2, v_v_1366_);
lean_ctor_set(v___x_1623_, 1, v_k_1365_);
lean_ctor_set(v___x_1623_, 0, v___x_1516_);
v___x_1634_ = v___x_1623_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_l_1602_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_l_1602_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v___x_1634_);
lean_ctor_set(v___x_1370_, 3, v___x_1632_);
lean_ctor_set(v___x_1370_, 2, v_v_1626_);
lean_ctor_set(v___x_1370_, 1, v_k_1625_);
lean_ctor_set(v___x_1370_, 0, v___x_1630_);
v___x_1636_ = v___x_1370_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1625_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1626_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(2u);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_r_1619_);
lean_ctor_set(v___x_1370_, 3, v_impl_1515_);
lean_ctor_set(v___x_1370_, 0, v___x_1648_);
v___x_1650_ = v___x_1370_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_impl_1515_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_r_1619_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_box_uint64(v_k_1361_);
v___x_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
lean_ctor_set(v___x_1655_, 2, v_v_1362_);
lean_ctor_set(v___x_1655_, 3, v_t_1363_);
lean_ctor_set(v___x_1655_, 4, v_t_1363_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1656_, lean_object* v_v_1657_, lean_object* v_t_1658_){
_start:
{
uint64_t v_k_boxed_1659_; lean_object* v_res_1660_; 
v_k_boxed_1659_ = lean_unbox_uint64(v_k_1656_);
lean_dec_ref(v_k_1656_);
v_res_1660_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1659_, v_v_1657_, v_t_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1661_, lean_object* v_s_1662_){
_start:
{
uint64_t v_javascriptHash_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_javascriptHash_1663_ = lean_ctor_get_uint64(v_wi_1661_, sizeof(void*)*2);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_wi_1661_);
v___x_1665_ = lean_box(0);
v___x_1666_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1662_, v_javascriptHash_1663_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1663_, v___x_1667_, v_s_1662_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___f_1673_; lean_object* v___x_1674_; lean_object* v_env_1675_; lean_object* v_nextMacroScope_1676_; lean_object* v_ngen_1677_; lean_object* v_auxDeclNGen_1678_; lean_object* v_traceState_1679_; lean_object* v_messages_1680_; lean_object* v_infoState_1681_; lean_object* v_snapshotTasks_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1710_; 
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1673_, 0, v_wi_1669_);
v___x_1674_ = lean_st_ref_take(v___y_1671_);
v_env_1675_ = lean_ctor_get(v___x_1674_, 0);
v_nextMacroScope_1676_ = lean_ctor_get(v___x_1674_, 1);
v_ngen_1677_ = lean_ctor_get(v___x_1674_, 2);
v_auxDeclNGen_1678_ = lean_ctor_get(v___x_1674_, 3);
v_traceState_1679_ = lean_ctor_get(v___x_1674_, 4);
v_messages_1680_ = lean_ctor_get(v___x_1674_, 6);
v_infoState_1681_ = lean_ctor_get(v___x_1674_, 7);
v_snapshotTasks_1682_ = lean_ctor_get(v___x_1674_, 8);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1674_, 5);
lean_dec(v_unused_1711_);
v___x_1684_ = v___x_1674_;
v_isShared_1685_ = v_isSharedCheck_1710_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_snapshotTasks_1682_);
lean_inc(v_infoState_1681_);
lean_inc(v_messages_1680_);
lean_inc(v_traceState_1679_);
lean_inc(v_auxDeclNGen_1678_);
lean_inc(v_ngen_1677_);
lean_inc(v_nextMacroScope_1676_);
lean_inc(v_env_1675_);
lean_dec(v___x_1674_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1710_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1686_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1687_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1686_, v_env_1675_, v___f_1673_);
v___x_1688_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 5, v___x_1688_);
lean_ctor_set(v___x_1684_, 0, v___x_1687_);
v___x_1690_ = v___x_1684_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_nextMacroScope_1676_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_ngen_1677_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_auxDeclNGen_1678_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_traceState_1679_);
lean_ctor_set(v_reuseFailAlloc_1709_, 5, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1709_, 6, v_messages_1680_);
lean_ctor_set(v_reuseFailAlloc_1709_, 7, v_infoState_1681_);
lean_ctor_set(v_reuseFailAlloc_1709_, 8, v_snapshotTasks_1682_);
v___x_1690_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_mctx_1693_; lean_object* v_zetaDeltaFVarIds_1694_; lean_object* v_postponed_1695_; lean_object* v_diag_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1707_; 
v___x_1691_ = lean_st_ref_put(v___y_1671_, v___x_1690_);
v___x_1692_ = lean_st_ref_take(v___y_1670_);
v_mctx_1693_ = lean_ctor_get(v___x_1692_, 0);
v_zetaDeltaFVarIds_1694_ = lean_ctor_get(v___x_1692_, 2);
v_postponed_1695_ = lean_ctor_get(v___x_1692_, 3);
v_diag_1696_ = lean_ctor_get(v___x_1692_, 4);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___x_1692_, 1);
lean_dec(v_unused_1708_);
v___x_1698_ = v___x_1692_;
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_diag_1696_);
lean_inc(v_postponed_1695_);
lean_inc(v_zetaDeltaFVarIds_1694_);
lean_inc(v_mctx_1693_);
lean_dec(v___x_1692_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1701_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_mctx_1693_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_zetaDeltaFVarIds_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_postponed_1695_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_diag_1696_);
v___x_1703_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_st_ref_put(v___y_1670_, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1700_);
return v___x_1705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(lean_object* v_ext_1717_, lean_object* v_b_1718_, uint8_t v_kind_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_toCold_1724_; lean_object* v_currNamespace_1725_; lean_object* v___x_1726_; lean_object* v_env_1727_; lean_object* v_nextMacroScope_1728_; lean_object* v_ngen_1729_; lean_object* v_auxDeclNGen_1730_; lean_object* v_traceState_1731_; lean_object* v_messages_1732_; lean_object* v_infoState_1733_; lean_object* v_snapshotTasks_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1761_; 
v_toCold_1724_ = lean_ctor_get(v___y_1721_, 0);
v_currNamespace_1725_ = lean_ctor_get(v_toCold_1724_, 4);
v___x_1726_ = lean_st_ref_take(v___y_1722_);
v_env_1727_ = lean_ctor_get(v___x_1726_, 0);
v_nextMacroScope_1728_ = lean_ctor_get(v___x_1726_, 1);
v_ngen_1729_ = lean_ctor_get(v___x_1726_, 2);
v_auxDeclNGen_1730_ = lean_ctor_get(v___x_1726_, 3);
v_traceState_1731_ = lean_ctor_get(v___x_1726_, 4);
v_messages_1732_ = lean_ctor_get(v___x_1726_, 6);
v_infoState_1733_ = lean_ctor_get(v___x_1726_, 7);
v_snapshotTasks_1734_ = lean_ctor_get(v___x_1726_, 8);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1726_, 5);
lean_dec(v_unused_1762_);
v___x_1736_ = v___x_1726_;
v_isShared_1737_ = v_isSharedCheck_1761_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snapshotTasks_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_traceState_1731_);
lean_inc(v_auxDeclNGen_1730_);
lean_inc(v_ngen_1729_);
lean_inc(v_nextMacroScope_1728_);
lean_inc(v_env_1727_);
lean_dec(v___x_1726_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1761_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_inc(v_currNamespace_1725_);
v___x_1738_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1727_, v_ext_1717_, v_b_1718_, v_kind_1719_, v_currNamespace_1725_);
v___x_1739_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 5, v___x_1739_);
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1741_ = v___x_1736_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_nextMacroScope_1728_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_ngen_1729_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_auxDeclNGen_1730_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_traceState_1731_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v_messages_1732_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_infoState_1733_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_snapshotTasks_1734_);
v___x_1741_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_mctx_1744_; lean_object* v_zetaDeltaFVarIds_1745_; lean_object* v_postponed_1746_; lean_object* v_diag_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1758_; 
v___x_1742_ = lean_st_ref_put(v___y_1722_, v___x_1741_);
v___x_1743_ = lean_st_ref_take(v___y_1720_);
v_mctx_1744_ = lean_ctor_get(v___x_1743_, 0);
v_zetaDeltaFVarIds_1745_ = lean_ctor_get(v___x_1743_, 2);
v_postponed_1746_ = lean_ctor_get(v___x_1743_, 3);
v_diag_1747_ = lean_ctor_get(v___x_1743_, 4);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v___x_1743_, 1);
lean_dec(v_unused_1759_);
v___x_1749_ = v___x_1743_;
v_isShared_1750_ = v_isSharedCheck_1758_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_diag_1747_);
lean_inc(v_postponed_1746_);
lean_inc(v_zetaDeltaFVarIds_1745_);
lean_inc(v_mctx_1744_);
lean_dec(v___x_1743_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1758_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1752_);
v___x_1754_ = v___x_1749_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_mctx_1744_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_zetaDeltaFVarIds_1745_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_postponed_1746_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_diag_1747_);
v___x_1754_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_st_ref_put(v___y_1720_, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1751_);
return v___x_1756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(lean_object* v_ext_1763_, lean_object* v_b_1764_, lean_object* v_kind_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v_kind_boxed_1770_; lean_object* v_res_1771_; 
v_kind_boxed_1770_ = lean_unbox(v_kind_1765_);
v_res_1771_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_1763_, v_b_1764_, v_kind_boxed_1770_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1772_, lean_object* v_n_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1782_ = lean_box_uint64(v_h_1772_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_n_1773_);
v___x_1784_ = 2;
v___x_1785_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1781_, v___x_1783_, v___x_1784_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1786_, lean_object* v_n_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint64_t v_h_boxed_1795_; lean_object* v_res_1796_; 
v_h_boxed_1795_ = lean_unbox_uint64(v_h_1786_);
lean_dec_ref(v_h_1786_);
v_res_1796_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1795_, v_n_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1797_, lean_object* v_n_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1806_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1807_ = lean_box_uint64(v_h_1797_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_n_1798_);
v___x_1809_ = 0;
v___x_1810_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1806_, v___x_1808_, v___x_1809_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1811_, lean_object* v_n_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint64_t v_h_boxed_1820_; lean_object* v_res_1821_; 
v_h_boxed_1820_ = lean_unbox_uint64(v_h_1811_);
lean_dec_ref(v_h_1811_);
v_res_1821_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1820_, v_n_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1822_, lean_object* v_declName_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v___x_1826_; lean_object* v_env_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; uint8_t v___x_1830_; 
v___x_1826_ = 0;
v_env_1827_ = l_Lean_Environment_setExporting(v_env_1822_, v___x_1826_);
lean_inc(v_declName_1823_);
v___x_1828_ = l_Lean_mkPrivateName(v_env_1827_, v_declName_1823_);
v___x_1829_ = 1;
lean_inc_ref(v_env_1827_);
v___x_1830_ = l_Lean_Environment_contains(v_env_1827_, v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = l_Lean_privateToUserName(v_declName_1823_);
v___x_1832_ = l_Lean_Environment_contains(v_env_1827_, v___x_1831_, v___x_1829_);
v___x_1833_ = lean_box(v___x_1832_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___y_1825_);
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v_env_1827_);
lean_dec(v_declName_1823_);
v___x_1835_ = lean_box(v___x_1830_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v___y_1825_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1837_, lean_object* v_declName_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1837_, v_declName_1838_, v___y_1839_, v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(lean_object* v_msgData_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v_env_1849_; lean_object* v___x_1850_; lean_object* v_toCold_1851_; lean_object* v_mctx_1852_; lean_object* v_lctx_1853_; lean_object* v_options_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1848_ = lean_st_ref_get(v___y_1846_);
v_env_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref(v_env_1849_);
lean_dec(v___x_1848_);
v___x_1850_ = lean_st_ref_get(v___y_1844_);
v_toCold_1851_ = lean_ctor_get(v___y_1845_, 0);
v_mctx_1852_ = lean_ctor_get(v___x_1850_, 0);
lean_inc_ref(v_mctx_1852_);
lean_dec(v___x_1850_);
v_lctx_1853_ = lean_ctor_get(v___y_1843_, 2);
v_options_1854_ = lean_ctor_get(v_toCold_1851_, 2);
lean_inc_ref(v_options_1854_);
lean_inc_ref(v_lctx_1853_);
v___x_1855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1855_, 0, v_env_1849_);
lean_ctor_set(v___x_1855_, 1, v_mctx_1852_);
lean_ctor_set(v___x_1855_, 2, v_lctx_1853_);
lean_ctor_set(v___x_1855_, 3, v_options_1854_);
v___x_1856_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_msgData_1842_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object* v_msgData_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1864_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1865_; double v___x_1866_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_float_of_nat(v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1869_, lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_ref_1876_; lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1922_; 
v_ref_1876_ = lean_ctor_get(v___y_1873_, 2);
v___x_1877_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1922_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1922_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v_traceState_1883_; lean_object* v_env_1884_; lean_object* v_nextMacroScope_1885_; lean_object* v_ngen_1886_; lean_object* v_auxDeclNGen_1887_; lean_object* v_cache_1888_; lean_object* v_messages_1889_; lean_object* v_infoState_1890_; lean_object* v_snapshotTasks_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1921_; 
v___x_1882_ = lean_st_ref_take(v___y_1874_);
v_traceState_1883_ = lean_ctor_get(v___x_1882_, 4);
v_env_1884_ = lean_ctor_get(v___x_1882_, 0);
v_nextMacroScope_1885_ = lean_ctor_get(v___x_1882_, 1);
v_ngen_1886_ = lean_ctor_get(v___x_1882_, 2);
v_auxDeclNGen_1887_ = lean_ctor_get(v___x_1882_, 3);
v_cache_1888_ = lean_ctor_get(v___x_1882_, 5);
v_messages_1889_ = lean_ctor_get(v___x_1882_, 6);
v_infoState_1890_ = lean_ctor_get(v___x_1882_, 7);
v_snapshotTasks_1891_ = lean_ctor_get(v___x_1882_, 8);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1893_ = v___x_1882_;
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snapshotTasks_1891_);
lean_inc(v_infoState_1890_);
lean_inc(v_messages_1889_);
lean_inc(v_cache_1888_);
lean_inc(v_traceState_1883_);
lean_inc(v_auxDeclNGen_1887_);
lean_inc(v_ngen_1886_);
lean_inc(v_nextMacroScope_1885_);
lean_inc(v_env_1884_);
lean_dec(v___x_1882_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
uint64_t v_tid_1895_; lean_object* v_traces_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1920_; 
v_tid_1895_ = lean_ctor_get_uint64(v_traceState_1883_, sizeof(void*)*1);
v_traces_1896_ = lean_ctor_get(v_traceState_1883_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_traceState_1883_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1898_ = v_traceState_1883_;
v_isShared_1899_ = v_isSharedCheck_1920_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_traces_1896_);
lean_dec(v_traceState_1883_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1920_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; double v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1903_ = 0;
v___x_1904_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1905_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1905_, 0, v_cls_1869_);
lean_ctor_set(v___x_1905_, 1, v___x_1901_);
lean_ctor_set(v___x_1905_, 2, v___x_1904_);
lean_ctor_set_float(v___x_1905_, sizeof(void*)*3, v___x_1902_);
lean_ctor_set_float(v___x_1905_, sizeof(void*)*3 + 8, v___x_1902_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*3 + 16, v___x_1903_);
v___x_1906_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1907_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v_a_1878_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
lean_inc(v_ref_1876_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_ref_1876_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_PersistentArray_push___redArg(v_traces_1896_, v___x_1908_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1909_);
v___x_1911_ = v___x_1898_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1909_);
lean_ctor_set_uint64(v_reuseFailAlloc_1919_, sizeof(void*)*1, v_tid_1895_);
v___x_1911_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v___x_1911_);
v___x_1913_ = v___x_1893_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_env_1884_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_nextMacroScope_1885_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_ngen_1886_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_auxDeclNGen_1887_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_cache_1888_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_messages_1889_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_infoState_1890_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_snapshotTasks_1891_);
v___x_1913_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_st_ref_put(v___y_1874_, v___x_1913_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1900_);
v___x_1916_ = v___x_1880_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1900_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1923_, lean_object* v_msg_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1923_, v_msg_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
if (lean_obj_tag(v_as_1934_) == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
else
{
lean_object* v_toCold_1944_; lean_object* v_options_1945_; uint8_t v_hasTrace_1946_; 
v_toCold_1944_ = lean_ctor_get(v___y_1939_, 0);
v_options_1945_ = lean_ctor_get(v_toCold_1944_, 2);
v_hasTrace_1946_ = lean_ctor_get_uint8(v_options_1945_, sizeof(void*)*1);
if (v_hasTrace_1946_ == 0)
{
lean_object* v_tail_1947_; 
v_tail_1947_ = lean_ctor_get(v_as_1934_, 1);
lean_inc(v_tail_1947_);
lean_dec_ref_known(v_as_1934_, 2);
v_as_1934_ = v_tail_1947_;
goto _start;
}
else
{
lean_object* v_head_1949_; lean_object* v_tail_1950_; lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v_inheritedTraceOptions_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_head_1949_ = lean_ctor_get(v_as_1934_, 0);
lean_inc(v_head_1949_);
v_tail_1950_ = lean_ctor_get(v_as_1934_, 1);
lean_inc(v_tail_1950_);
lean_dec_ref_known(v_as_1934_, 2);
v_fst_1951_ = lean_ctor_get(v_head_1949_, 0);
lean_inc_n(v_fst_1951_, 2);
v_snd_1952_ = lean_ctor_get(v_head_1949_, 1);
lean_inc(v_snd_1952_);
lean_dec(v_head_1949_);
v_inheritedTraceOptions_1953_ = lean_ctor_get(v_toCold_1944_, 11);
v___x_1954_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_1955_ = l_Lean_Name_append(v___x_1954_, v_fst_1951_);
v___x_1956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1953_, v_options_1945_, v___x_1955_);
lean_dec(v___x_1955_);
if (v___x_1956_ == 0)
{
lean_dec(v_snd_1952_);
lean_dec(v_fst_1951_);
v_as_1934_ = v_tail_1950_;
goto _start;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_snd_1952_);
v___x_1959_ = l_Lean_MessageData_ofFormat(v___x_1958_);
v___x_1960_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_1951_, v___x_1959_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref_known(v___x_1960_, 1);
v_as_1934_ = v_tail_1950_;
goto _start;
}
else
{
lean_dec(v_tail_1950_);
return v___x_1960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_env_1971_, lean_object* v_currNamespace_1972_, lean_object* v_openDecls_1973_, lean_object* v_n_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = l_Lean_ResolveName_resolveNamespace(v_env_1971_, v_currNamespace_1972_, v_openDecls_1973_, v_n_1974_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_env_1979_, lean_object* v_currNamespace_1980_, lean_object* v_openDecls_1981_, lean_object* v_n_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_env_1979_, v_currNamespace_1980_, v_openDecls_1981_, v_n_1982_, v___y_1983_, v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object* v_opts_1986_, lean_object* v_opt_1987_){
_start:
{
lean_object* v_name_1988_; lean_object* v_defValue_1989_; lean_object* v_map_1990_; lean_object* v___x_1991_; 
v_name_1988_ = lean_ctor_get(v_opt_1987_, 0);
v_defValue_1989_ = lean_ctor_get(v_opt_1987_, 1);
v_map_1990_ = lean_ctor_get(v_opts_1986_, 0);
v___x_1991_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1990_, v_name_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_unbox(v_defValue_1989_);
return v___x_1992_;
}
else
{
lean_object* v_val_1993_; 
v_val_1993_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v___x_1991_, 1);
if (lean_obj_tag(v_val_1993_) == 1)
{
uint8_t v_v_1994_; 
v_v_1994_ = lean_ctor_get_uint8(v_val_1993_, 0);
lean_dec_ref_known(v_val_1993_, 0);
return v_v_1994_;
}
else
{
uint8_t v___x_1995_; 
lean_dec(v_val_1993_);
v___x_1995_ = lean_unbox(v_defValue_1989_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object* v_opts_1996_, lean_object* v_opt_1997_){
_start:
{
uint8_t v_res_1998_; lean_object* v_r_1999_; 
v_res_1998_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_1996_, v_opt_1997_);
lean_dec_ref(v_opt_1997_);
lean_dec_ref(v_opts_1996_);
v_r_1999_ = lean_box(v_res_1998_);
return v_r_1999_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_box(1);
v___x_2001_ = l_Lean_MessageData_ofFormat(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2));
v___x_2006_ = l_Lean_MessageData_ofFormat(v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
return v_x_2007_;
}
else
{
lean_object* v_head_2009_; lean_object* v_tail_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2032_; 
v_head_2009_ = lean_ctor_get(v_x_2008_, 0);
v_tail_2010_ = lean_ctor_get(v_x_2008_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2012_ = v_x_2008_;
v_isShared_2013_ = v_isSharedCheck_2032_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_tail_2010_);
lean_inc(v_head_2009_);
lean_dec(v_x_2008_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2032_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_before_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2030_; 
v_before_2014_ = lean_ctor_get(v_head_2009_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_head_2009_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_head_2009_, 1);
lean_dec(v_unused_2031_);
v___x_2016_ = v_head_2009_;
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_before_2014_);
lean_dec(v_head_2009_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 7);
lean_ctor_set(v___x_2016_, 1, v___x_2018_);
lean_ctor_set(v___x_2016_, 0, v_x_2007_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_x_2007_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 7);
lean_ctor_set(v___x_2012_, 1, v___x_2021_);
lean_ctor_set(v___x_2012_, 0, v___x_2020_);
v___x_2023_ = v___x_2012_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = l_Lean_MessageData_ofSyntax(v_before_2014_);
v___x_2025_ = l_Lean_indentD(v___x_2024_);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2023_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v_x_2007_ = v___x_2026_;
v_x_2008_ = v_tail_2010_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1));
v___x_2037_ = l_Lean_MessageData_ofFormat(v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object* v_msgData_2038_, lean_object* v_macroStack_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_toCold_2042_; lean_object* v_options_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_toCold_2042_ = lean_ctor_get(v___y_2040_, 0);
v_options_2043_ = lean_ctor_get(v_toCold_2042_, 2);
v___x_2044_ = l_Lean_Elab_pp_macroStack;
v___x_2045_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_options_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v_macroStack_2039_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_msgData_2038_);
return v___x_2046_;
}
else
{
if (lean_obj_tag(v_macroStack_2039_) == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_msgData_2038_);
return v___x_2047_;
}
else
{
lean_object* v_head_2048_; lean_object* v_after_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2064_; 
v_head_2048_ = lean_ctor_get(v_macroStack_2039_, 0);
lean_inc(v_head_2048_);
v_after_2049_ = lean_ctor_get(v_head_2048_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_head_2048_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_head_2048_, 0);
lean_dec(v_unused_2065_);
v___x_2051_ = v_head_2048_;
v_isShared_2052_ = v_isSharedCheck_2064_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_after_2049_);
lean_dec(v_head_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2064_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 7);
lean_ctor_set(v___x_2051_, 1, v___x_2053_);
lean_ctor_set(v___x_2051_, 0, v_msgData_2038_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_msgData_2038_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_msgData_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2056_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
v___x_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = l_Lean_MessageData_ofSyntax(v_after_2049_);
v___x_2059_ = l_Lean_indentD(v___x_2058_);
v_msgData_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2060_, 0, v___x_2057_);
lean_ctor_set(v_msgData_2060_, 1, v___x_2059_);
v___x_2061_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_2060_, v_macroStack_2039_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object* v_msgData_2066_, lean_object* v_macroStack_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2066_, v_macroStack_2067_, v___y_2068_);
lean_dec_ref(v___y_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_ref_2079_; lean_object* v_macroStack_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2093_; 
v_ref_2079_ = lean_ctor_get(v___y_2076_, 2);
v_macroStack_2080_ = lean_ctor_get(v___y_2072_, 1);
v___x_2081_ = l_Lean_Elab_getBetterRef(v_ref_2079_, v_macroStack_2080_);
v___x_2082_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_2071_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2082_);
lean_inc(v_macroStack_2080_);
v___x_2084_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_2083_, v_macroStack_2080_, v___y_2076_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2081_);
lean_ctor_set(v___x_2089_, 1, v_a_2085_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 1);
lean_ctor_set(v___x_2087_, 0, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2103_, lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_toCold_2112_; lean_object* v_currRecDepth_2113_; lean_object* v_ref_2114_; uint8_t v_diag_2115_; uint8_t v_suppressElabErrors_2116_; lean_object* v_ref_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_toCold_2112_ = lean_ctor_get(v___y_2109_, 0);
v_currRecDepth_2113_ = lean_ctor_get(v___y_2109_, 1);
v_ref_2114_ = lean_ctor_get(v___y_2109_, 2);
v_diag_2115_ = lean_ctor_get_uint8(v___y_2109_, sizeof(void*)*3);
v_suppressElabErrors_2116_ = lean_ctor_get_uint8(v___y_2109_, sizeof(void*)*3 + 1);
v_ref_2117_ = l_Lean_replaceRef(v_ref_2103_, v_ref_2114_);
lean_inc(v_currRecDepth_2113_);
lean_inc_ref(v_toCold_2112_);
v___x_2118_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2118_, 0, v_toCold_2112_);
lean_ctor_set(v___x_2118_, 1, v_currRecDepth_2113_);
lean_ctor_set(v___x_2118_, 2, v_ref_2117_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*3, v_diag_2115_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*3 + 1, v_suppressElabErrors_2116_);
v___x_2119_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___x_2118_, v___y_2110_);
lean_dec_ref_known(v___x_2118_, 3);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2120_, lean_object* v_msg_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2120_, v_msg_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v_ref_2120_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2130_, lean_object* v_options_2131_, lean_object* v_currNamespace_2132_, lean_object* v_openDecls_2133_, lean_object* v_n_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = l_Lean_ResolveName_resolveGlobalName(v_env_2130_, v_options_2131_, v_currNamespace_2132_, v_openDecls_2133_, v_n_2134_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2139_, lean_object* v_options_2140_, lean_object* v_currNamespace_2141_, lean_object* v_openDecls_2142_, lean_object* v_n_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2139_, v_options_2140_, v_currNamespace_2141_, v_openDecls_2142_, v_n_2143_, v___y_2144_, v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec_ref(v_options_2140_);
return v_res_2146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object* v_keys_2147_, lean_object* v_i_2148_, lean_object* v_k_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_array_get_size(v_keys_2147_);
v___x_2151_ = lean_nat_dec_lt(v_i_2148_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec(v_i_2148_);
return v___x_2151_;
}
else
{
lean_object* v_k_x27_2152_; uint8_t v___x_2153_; 
v_k_x27_2152_ = lean_array_fget_borrowed(v_keys_2147_, v_i_2148_);
v___x_2153_ = l_Lean_instBEqExtraModUse_beq(v_k_2149_, v_k_x27_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(1u);
v___x_2155_ = lean_nat_add(v_i_2148_, v___x_2154_);
lean_dec(v_i_2148_);
v_i_2148_ = v___x_2155_;
goto _start;
}
else
{
lean_dec(v_i_2148_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object* v_keys_2157_, lean_object* v_i_2158_, lean_object* v_k_2159_){
_start:
{
uint8_t v_res_2160_; lean_object* v_r_2161_; 
v_res_2160_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2157_, v_i_2158_, v_k_2159_);
lean_dec_ref(v_k_2159_);
lean_dec_ref(v_keys_2157_);
v_r_2161_ = lean_box(v_res_2160_);
return v_r_2161_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object* v_x_2162_, size_t v_x_2163_, lean_object* v_x_2164_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v_es_2165_; lean_object* v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; lean_object* v_j_2169_; lean_object* v___x_2170_; 
v_es_2165_ = lean_ctor_get(v_x_2162_, 0);
v___x_2166_ = lean_box(2);
v___x_2167_ = ((size_t)31ULL);
v___x_2168_ = lean_usize_land(v_x_2163_, v___x_2167_);
v_j_2169_ = lean_usize_to_nat(v___x_2168_);
v___x_2170_ = lean_array_get_borrowed(v___x_2166_, v_es_2165_, v_j_2169_);
lean_dec(v_j_2169_);
switch(lean_obj_tag(v___x_2170_))
{
case 0:
{
lean_object* v_key_2171_; uint8_t v___x_2172_; 
v_key_2171_ = lean_ctor_get(v___x_2170_, 0);
v___x_2172_ = l_Lean_instBEqExtraModUse_beq(v_x_2164_, v_key_2171_);
return v___x_2172_;
}
case 1:
{
lean_object* v_node_2173_; size_t v___x_2174_; size_t v___x_2175_; 
v_node_2173_ = lean_ctor_get(v___x_2170_, 0);
v___x_2174_ = ((size_t)5ULL);
v___x_2175_ = lean_usize_shift_right(v_x_2163_, v___x_2174_);
v_x_2162_ = v_node_2173_;
v_x_2163_ = v___x_2175_;
goto _start;
}
default: 
{
uint8_t v___x_2177_; 
v___x_2177_ = 0;
return v___x_2177_;
}
}
}
else
{
lean_object* v_ks_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_ks_2178_ = lean_ctor_get(v_x_2162_, 0);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_2178_, v___x_2179_, v_x_2164_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
size_t v_x_29407__boxed_2184_; uint8_t v_res_2185_; lean_object* v_r_2186_; 
v_x_29407__boxed_2184_ = lean_unbox_usize(v_x_2182_);
lean_dec(v_x_2182_);
v_res_2185_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2181_, v_x_29407__boxed_2184_, v_x_2183_);
lean_dec_ref(v_x_2183_);
lean_dec_ref(v_x_2181_);
v_r_2186_ = lean_box(v_res_2185_);
return v_r_2186_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
uint64_t v___x_2189_; size_t v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = l_Lean_instHashableExtraModUse_hash(v_x_2188_);
v___x_2190_ = lean_uint64_to_usize(v___x_2189_);
v___x_2191_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2187_, v___x_2190_, v_x_2188_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
uint8_t v_res_2194_; lean_object* v_r_2195_; 
v_res_2194_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2192_, v_x_2193_);
lean_dec_ref(v_x_2193_);
lean_dec_ref(v_x_2192_);
v_r_2195_ = lean_box(v_res_2194_);
return v_r_2195_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v_cls_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_cls_2208_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2209_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2210_ = l_Lean_Name_append(v___x_2209_, v_cls_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2216_ = l_Lean_stringToMessageData(v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2221_, uint8_t v_isMeta_2222_, lean_object* v_hint_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v_env_2233_; uint8_t v_isExporting_2234_; lean_object* v_entry_2235_; lean_object* v___x_2236_; lean_object* v_env_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2231_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0);
v___x_2232_ = lean_st_ref_get(v___y_2229_);
v_env_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc_ref(v_env_2233_);
lean_dec(v___x_2232_);
v_isExporting_2234_ = lean_ctor_get_uint8(v_env_2233_, sizeof(void*)*8);
lean_dec_ref(v_env_2233_);
lean_inc(v_mod_2221_);
v_entry_2235_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2235_, 0, v_mod_2221_);
lean_ctor_set_uint8(v_entry_2235_, sizeof(void*)*1, v_isExporting_2234_);
lean_ctor_set_uint8(v_entry_2235_, sizeof(void*)*1 + 1, v_isMeta_2222_);
v___x_2236_ = lean_st_ref_get(v___y_2229_);
v_env_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc_ref(v_env_2237_);
lean_dec(v___x_2236_);
v___x_2238_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2239_ = lean_box(1);
v___x_2240_ = lean_box(0);
v___x_2283_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2231_, v___x_2238_, v_env_2237_, v___x_2239_, v___x_2240_);
v___x_2284_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_2283_, v_entry_2235_);
lean_dec(v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v_toCold_2285_; lean_object* v_options_2286_; uint8_t v_hasTrace_2287_; 
v_toCold_2285_ = lean_ctor_get(v___y_2228_, 0);
v_options_2286_ = lean_ctor_get(v_toCold_2285_, 2);
v_hasTrace_2287_ = lean_ctor_get_uint8(v_options_2286_, sizeof(void*)*1);
if (v_hasTrace_2287_ == 0)
{
lean_dec(v_hint_2223_);
lean_dec(v_mod_2221_);
v___y_2242_ = v___y_2227_;
v___y_2243_ = v___y_2229_;
goto v___jp_2241_;
}
else
{
lean_object* v_inheritedTraceOptions_2288_; lean_object* v_cls_2289_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_inheritedTraceOptions_2288_ = lean_ctor_get(v_toCold_2285_, 11);
v_cls_2289_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2309_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2288_, v_options_2286_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_dec(v_hint_2223_);
lean_dec(v_mod_2221_);
v___y_2242_ = v___y_2227_;
v___y_2243_ = v___y_2229_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2311_; lean_object* v___y_2313_; 
v___x_2311_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
if (v_isExporting_2234_ == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2313_ = v___x_2320_;
goto v___jp_2312_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2313_ = v___x_2321_;
goto v___jp_2312_;
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_inc_ref(v___y_2313_);
v___x_2314_ = l_Lean_stringToMessageData(v___y_2313_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2311_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
if (v_isMeta_2222_ == 0)
{
lean_object* v___x_2318_; 
v___x_2318_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___y_2296_ = v___x_2317_;
v___y_2297_ = v___x_2318_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2319_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14));
v___y_2296_ = v___x_2317_;
v___y_2297_ = v___x_2319_;
goto v___jp_2295_;
}
}
}
v___jp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___y_2291_);
lean_ctor_set(v___x_2293_, 1, v___y_2292_);
v___x_2294_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2289_, v___x_2293_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref_known(v___x_2294_, 1);
v___y_2242_ = v___y_2227_;
v___y_2243_ = v___y_2229_;
goto v___jp_2241_;
}
else
{
lean_dec_ref_known(v_entry_2235_, 1);
return v___x_2294_;
}
}
v___jp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
lean_inc_ref(v___y_2297_);
v___x_2298_ = l_Lean_stringToMessageData(v___y_2297_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2296_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_MessageData_ofName(v_mod_2221_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_Name_isAnonymous(v_hint_2223_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2306_ = l_Lean_MessageData_ofName(v_hint_2223_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___y_2291_ = v___x_2303_;
v___y_2292_ = v___x_2307_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2308_; 
lean_dec(v_hint_2223_);
v___x_2308_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7);
v___y_2291_ = v___x_2303_;
v___y_2292_ = v___x_2308_;
goto v___jp_2290_;
}
}
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref_known(v_entry_2235_, 1);
lean_dec(v_hint_2223_);
lean_dec(v_mod_2221_);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
v___jp_2241_:
{
lean_object* v___x_2244_; lean_object* v_toEnvExtension_2245_; lean_object* v_env_2246_; lean_object* v_nextMacroScope_2247_; lean_object* v_ngen_2248_; lean_object* v_auxDeclNGen_2249_; lean_object* v_traceState_2250_; lean_object* v_messages_2251_; lean_object* v_infoState_2252_; lean_object* v_snapshotTasks_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2281_; 
v___x_2244_ = lean_st_ref_take(v___y_2243_);
v_toEnvExtension_2245_ = lean_ctor_get(v___x_2238_, 0);
v_env_2246_ = lean_ctor_get(v___x_2244_, 0);
v_nextMacroScope_2247_ = lean_ctor_get(v___x_2244_, 1);
v_ngen_2248_ = lean_ctor_get(v___x_2244_, 2);
v_auxDeclNGen_2249_ = lean_ctor_get(v___x_2244_, 3);
v_traceState_2250_ = lean_ctor_get(v___x_2244_, 4);
v_messages_2251_ = lean_ctor_get(v___x_2244_, 6);
v_infoState_2252_ = lean_ctor_get(v___x_2244_, 7);
v_snapshotTasks_2253_ = lean_ctor_get(v___x_2244_, 8);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v___x_2244_, 5);
lean_dec(v_unused_2282_);
v___x_2255_ = v___x_2244_;
v_isShared_2256_ = v_isSharedCheck_2281_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_snapshotTasks_2253_);
lean_inc(v_infoState_2252_);
lean_inc(v_messages_2251_);
lean_inc(v_traceState_2250_);
lean_inc(v_auxDeclNGen_2249_);
lean_inc(v_ngen_2248_);
lean_inc(v_nextMacroScope_2247_);
lean_inc(v_env_2246_);
lean_dec(v___x_2244_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2281_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_asyncMode_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v_asyncMode_2257_ = lean_ctor_get(v_toEnvExtension_2245_, 2);
v___x_2258_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2238_, v_env_2246_, v_entry_2235_, v_asyncMode_2257_, v___x_2240_);
v___x_2259_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 5, v___x_2259_);
lean_ctor_set(v___x_2255_, 0, v___x_2258_);
v___x_2261_ = v___x_2255_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_nextMacroScope_2247_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_ngen_2248_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_auxDeclNGen_2249_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_traceState_2250_);
lean_ctor_set(v_reuseFailAlloc_2280_, 5, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2280_, 6, v_messages_2251_);
lean_ctor_set(v_reuseFailAlloc_2280_, 7, v_infoState_2252_);
lean_ctor_set(v_reuseFailAlloc_2280_, 8, v_snapshotTasks_2253_);
v___x_2261_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_mctx_2264_; lean_object* v_zetaDeltaFVarIds_2265_; lean_object* v_postponed_2266_; lean_object* v_diag_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2278_; 
v___x_2262_ = lean_st_ref_put(v___y_2243_, v___x_2261_);
v___x_2263_ = lean_st_ref_take(v___y_2242_);
v_mctx_2264_ = lean_ctor_get(v___x_2263_, 0);
v_zetaDeltaFVarIds_2265_ = lean_ctor_get(v___x_2263_, 2);
v_postponed_2266_ = lean_ctor_get(v___x_2263_, 3);
v_diag_2267_ = lean_ctor_get(v___x_2263_, 4);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; 
v_unused_2279_ = lean_ctor_get(v___x_2263_, 1);
lean_dec(v_unused_2279_);
v___x_2269_ = v___x_2263_;
v_isShared_2270_ = v_isSharedCheck_2278_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_diag_2267_);
lean_inc(v_postponed_2266_);
lean_inc(v_zetaDeltaFVarIds_2265_);
lean_inc(v_mctx_2264_);
lean_dec(v___x_2263_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2278_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v___x_2272_);
v___x_2274_ = v___x_2269_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_mctx_2264_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_zetaDeltaFVarIds_2265_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_postponed_2266_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v_diag_2267_);
v___x_2274_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_st_ref_put(v___y_2242_, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2271_);
return v___x_2276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2324_, lean_object* v_isMeta_2325_, lean_object* v_hint_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v_isMeta_boxed_2334_; lean_object* v_res_2335_; 
v_isMeta_boxed_2334_ = lean_unbox(v_isMeta_2325_);
v_res_2335_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2324_, v_isMeta_boxed_2334_, v_hint_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2336_, lean_object* v_declName_2337_, lean_object* v_as_2338_, size_t v_sz_2339_, size_t v_i_2340_, lean_object* v_b_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_usize_dec_lt(v_i_2340_, v_sz_2339_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec(v_declName_2337_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_b_2341_);
return v___x_2350_;
}
else
{
lean_object* v___x_2351_; lean_object* v_modules_2352_; lean_object* v___x_2353_; lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v_toImport_2356_; lean_object* v_module_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2351_ = l_Lean_Environment_header(v___x_2336_);
v_modules_2352_ = lean_ctor_get(v___x_2351_, 3);
lean_inc_ref(v_modules_2352_);
lean_dec_ref(v___x_2351_);
v___x_2353_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2354_ = lean_array_uget_borrowed(v_as_2338_, v_i_2340_);
v___x_2355_ = lean_array_get(v___x_2353_, v_modules_2352_, v_a_2354_);
lean_dec_ref(v_modules_2352_);
v_toImport_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc_ref(v_toImport_2356_);
lean_dec(v___x_2355_);
v_module_2357_ = lean_ctor_get(v_toImport_2356_, 0);
lean_inc(v_module_2357_);
lean_dec_ref(v_toImport_2356_);
v___x_2358_ = lean_box(0);
v___x_2359_ = 0;
lean_inc(v_declName_2337_);
v___x_2360_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2357_, v___x_2359_, v_declName_2337_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2360_) == 0)
{
size_t v___x_2361_; size_t v___x_2362_; 
lean_dec_ref_known(v___x_2360_, 1);
v___x_2361_ = ((size_t)1ULL);
v___x_2362_ = lean_usize_add(v_i_2340_, v___x_2361_);
v_i_2340_ = v___x_2362_;
v_b_2341_ = v___x_2358_;
goto _start;
}
else
{
lean_dec(v_declName_2337_);
return v___x_2360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2364_, lean_object* v_declName_2365_, lean_object* v_as_2366_, lean_object* v_sz_2367_, lean_object* v_i_2368_, lean_object* v_b_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
size_t v_sz_boxed_2377_; size_t v_i_boxed_2378_; lean_object* v_res_2379_; 
v_sz_boxed_2377_ = lean_unbox_usize(v_sz_2367_);
lean_dec(v_sz_2367_);
v_i_boxed_2378_ = lean_unbox_usize(v_i_2368_);
lean_dec(v_i_2368_);
v_res_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2364_, v_declName_2365_, v_as_2366_, v_sz_boxed_2377_, v_i_boxed_2378_, v_b_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v_as_2366_);
lean_dec_ref(v___x_2364_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object* v_a_2380_, lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_box(0);
return v___x_2382_;
}
else
{
lean_object* v_key_2383_; lean_object* v_value_2384_; lean_object* v_tail_2385_; uint8_t v___x_2386_; 
v_key_2383_ = lean_ctor_get(v_x_2381_, 0);
v_value_2384_ = lean_ctor_get(v_x_2381_, 1);
v_tail_2385_ = lean_ctor_get(v_x_2381_, 2);
v___x_2386_ = lean_name_eq(v_key_2383_, v_a_2380_);
if (v___x_2386_ == 0)
{
v_x_2381_ = v_tail_2385_;
goto _start;
}
else
{
lean_object* v___x_2388_; 
lean_inc(v_value_2384_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_value_2384_);
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object* v_a_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2389_, v_x_2390_);
lean_dec(v_x_2390_);
lean_dec(v_a_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_buckets_2394_; lean_object* v___x_2395_; uint64_t v___y_2397_; 
v_buckets_2394_ = lean_ctor_get(v_m_2392_, 1);
v___x_2395_ = lean_array_get_size(v_buckets_2394_);
if (lean_obj_tag(v_a_2393_) == 0)
{
uint64_t v___x_2411_; 
v___x_2411_ = 1723ULL;
v___y_2397_ = v___x_2411_;
goto v___jp_2396_;
}
else
{
uint64_t v_hash_2412_; 
v_hash_2412_ = lean_ctor_get_uint64(v_a_2393_, sizeof(void*)*2);
v___y_2397_ = v_hash_2412_;
goto v___jp_2396_;
}
v___jp_2396_:
{
uint64_t v___x_2398_; uint64_t v___x_2399_; uint64_t v_fold_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; uint64_t v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; size_t v___x_2406_; size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2398_ = 32ULL;
v___x_2399_ = lean_uint64_shift_right(v___y_2397_, v___x_2398_);
v_fold_2400_ = lean_uint64_xor(v___y_2397_, v___x_2399_);
v___x_2401_ = 16ULL;
v___x_2402_ = lean_uint64_shift_right(v_fold_2400_, v___x_2401_);
v___x_2403_ = lean_uint64_xor(v_fold_2400_, v___x_2402_);
v___x_2404_ = lean_uint64_to_usize(v___x_2403_);
v___x_2405_ = lean_usize_of_nat(v___x_2395_);
v___x_2406_ = ((size_t)1ULL);
v___x_2407_ = lean_usize_sub(v___x_2405_, v___x_2406_);
v___x_2408_ = lean_usize_land(v___x_2404_, v___x_2407_);
v___x_2409_ = lean_array_uget_borrowed(v_buckets_2394_, v___x_2408_);
v___x_2410_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2393_, v___x_2409_);
return v___x_2410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_m_2413_);
return v_res_2415_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2419_, uint8_t v_isMeta_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_env_2433_; lean_object* v___y_2435_; lean_object* v___x_2448_; 
v___x_2428_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0);
v___x_2429_ = lean_st_ref_get(v___y_2426_);
v_env_2433_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_ref(v_env_2433_);
lean_dec(v___x_2429_);
v___x_2448_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2433_, v_declName_2419_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_dec_ref(v_env_2433_);
lean_dec(v_declName_2419_);
goto v___jp_2430_;
}
else
{
lean_object* v_val_2449_; lean_object* v___x_2450_; lean_object* v_modules_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v_val_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_val_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = l_Lean_Environment_header(v_env_2433_);
v_modules_2451_ = lean_ctor_get(v___x_2450_, 3);
lean_inc_ref(v_modules_2451_);
lean_dec_ref(v___x_2450_);
v___x_2452_ = lean_array_get_size(v_modules_2451_);
v___x_2453_ = lean_nat_dec_lt(v_val_2449_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_dec_ref(v_modules_2451_);
lean_dec(v_val_2449_);
lean_dec_ref(v_env_2433_);
lean_dec(v_declName_2419_);
goto v___jp_2430_;
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___y_2457_; 
v___x_2454_ = lean_array_fget(v_modules_2451_, v_val_2449_);
lean_dec(v_val_2449_);
lean_dec_ref(v_modules_2451_);
v___x_2455_ = lean_st_ref_get(v___y_2426_);
if (v_isMeta_2420_ == 0)
{
lean_dec(v___x_2455_);
v___y_2457_ = v_isMeta_2420_;
goto v___jp_2456_;
}
else
{
lean_object* v_env_2468_; uint8_t v___x_2469_; 
v_env_2468_ = lean_ctor_get(v___x_2455_, 0);
lean_inc_ref(v_env_2468_);
lean_dec(v___x_2455_);
lean_inc(v_declName_2419_);
v___x_2469_ = l_Lean_isMarkedMeta(v_env_2468_, v_declName_2419_);
if (v___x_2469_ == 0)
{
v___y_2457_ = v_isMeta_2420_;
goto v___jp_2456_;
}
else
{
uint8_t v___x_2470_; 
v___x_2470_ = 0;
v___y_2457_ = v___x_2470_;
goto v___jp_2456_;
}
}
v___jp_2456_:
{
lean_object* v_toImport_2458_; lean_object* v_module_2459_; lean_object* v___x_2460_; 
v_toImport_2458_ = lean_ctor_get(v___x_2454_, 0);
lean_inc_ref(v_toImport_2458_);
lean_dec(v___x_2454_);
v_module_2459_ = lean_ctor_get(v_toImport_2458_, 0);
lean_inc(v_module_2459_);
lean_dec_ref(v_toImport_2458_);
lean_inc(v_declName_2419_);
v___x_2460_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2459_, v___y_2457_, v_declName_2419_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_dec_ref_known(v___x_2460_, 1);
v___x_2461_ = l_Lean_indirectModUseExt;
v___x_2462_ = lean_box(1);
v___x_2463_ = lean_box(0);
lean_inc_ref(v_env_2433_);
v___x_2464_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2428_, v___x_2461_, v_env_2433_, v___x_2462_, v___x_2463_);
v___x_2465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2464_, v_declName_2419_);
lean_dec(v___x_2464_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v___x_2466_; 
v___x_2466_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___y_2435_ = v___x_2466_;
goto v___jp_2434_;
}
else
{
lean_object* v_val_2467_; 
v_val_2467_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v___x_2465_, 1);
v___y_2435_ = v_val_2467_;
goto v___jp_2434_;
}
}
else
{
lean_dec_ref(v_env_2433_);
lean_dec(v_declName_2419_);
return v___x_2460_;
}
}
}
}
v___jp_2430_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
v___jp_2434_:
{
lean_object* v___x_2436_; size_t v_sz_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2436_ = lean_box(0);
v_sz_2437_ = lean_array_size(v___y_2435_);
v___x_2438_ = ((size_t)0ULL);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2433_, v_declName_2419_, v___y_2435_, v_sz_2437_, v___x_2438_, v___x_2436_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_env_2433_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; 
v_unused_2447_ = lean_ctor_get(v___x_2439_, 0);
lean_dec(v_unused_2447_);
v___x_2441_ = v___x_2439_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_dec(v___x_2439_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2436_);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2436_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
return v___x_2439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2471_, lean_object* v_isMeta_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
uint8_t v_isMeta_boxed_2480_; lean_object* v_res_2481_; 
v_isMeta_boxed_2480_ = lean_unbox(v_isMeta_2472_);
v_res_2481_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2471_, v_isMeta_boxed_2480_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2482_, lean_object* v_b_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
if (lean_obj_tag(v_as_x27_2482_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_b_2483_);
return v___x_2491_;
}
else
{
lean_object* v_head_2492_; lean_object* v_tail_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; 
v_head_2492_ = lean_ctor_get(v_as_x27_2482_, 0);
v_tail_2493_ = lean_ctor_get(v_as_x27_2482_, 1);
v___x_2494_ = lean_box(0);
v___x_2495_ = 1;
lean_inc(v_head_2492_);
v___x_2496_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2492_, v___x_2495_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_dec_ref_known(v___x_2496_, 1);
v_as_x27_2482_ = v_tail_2493_;
v_b_2483_ = v___x_2494_;
goto _start;
}
else
{
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2498_, v_b_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v_as_x27_2498_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_currNamespace_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_currNamespace_2508_);
lean_ctor_set(v___x_2511_, 1, v___y_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_currNamespace_2512_, v___y_2513_, v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_2516_, lean_object* v___y_2517_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_a_2518_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_a_2518_);
lean_ctor_set(v___x_2519_, 1, v___y_2517_);
return v___x_2519_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2521_; 
v_a_2520_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_a_2520_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_a_2520_);
lean_ctor_set(v___x_2521_, 1, v___y_2517_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2522_, v___y_2523_);
lean_dec_ref(v_x_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2525_, lean_object* v_stx_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2525_, v_stx_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
if (lean_obj_tag(v_a_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_a_2531_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v___x_2529_, 0);
lean_dec(v_unused_2540_);
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_a_2531_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2569_; 
v_val_2541_ = lean_ctor_get(v_a_2530_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2543_ = v_a_2530_;
v_isShared_2544_ = v_isSharedCheck_2569_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v_a_2530_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2569_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_snd_2545_; 
v_snd_2545_ = lean_ctor_get(v_val_2541_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_val_2541_);
if (lean_obj_tag(v_snd_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2555_; 
lean_del_object(v___x_2543_);
v_a_2546_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2529_, 2);
v_a_2547_ = lean_ctor_get(v_snd_2545_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_snd_2545_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2549_ = v_snd_2545_;
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v_snd_2545_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2552_, v_a_2546_);
lean_dec_ref(v___x_2552_);
return v___x_2553_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2568_; 
v_a_2556_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2529_, 2);
v_a_2557_ = lean_ctor_get(v_snd_2545_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_snd_2545_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2559_ = v_snd_2545_;
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v_snd_2545_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v_a_2557_);
v___x_2562_ = v___x_2543_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2562_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2564_, v_a_2556_);
lean_dec_ref(v___x_2564_);
return v___x_2565_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_a_2570_ = lean_ctor_get(v___x_2529_, 0);
v_a_2571_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2529_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_inc(v_a_2570_);
lean_dec(v___x_2529_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2579_, lean_object* v_stx_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2579_, v_stx_2580_, v___y_2581_, v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2583_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = l_Lean_maxRecDepthErrorMessage;
v___x_2590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2592_ = l_Lean_MessageData_ofFormat(v___x_2591_);
return v___x_2592_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2594_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2595_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_ref_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; lean_object* v_toCold_2614_; lean_object* v_env_2615_; lean_object* v_currRecDepth_2616_; lean_object* v_ref_2617_; lean_object* v_options_2618_; lean_object* v_maxRecDepth_2619_; lean_object* v_currNamespace_2620_; lean_object* v_openDecls_2621_; lean_object* v_quotContext_2622_; lean_object* v_currMacroScope_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v_methods_2629_; lean_object* v___x_2630_; lean_object* v_nextMacroScope_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2613_ = lean_st_ref_get(v___y_2611_);
v_toCold_2614_ = lean_ctor_get(v___y_2610_, 0);
v_env_2615_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_ref_n(v_env_2615_, 4);
lean_dec(v___x_2613_);
v_currRecDepth_2616_ = lean_ctor_get(v___y_2610_, 1);
v_ref_2617_ = lean_ctor_get(v___y_2610_, 2);
v_options_2618_ = lean_ctor_get(v_toCold_2614_, 2);
v_maxRecDepth_2619_ = lean_ctor_get(v_toCold_2614_, 3);
v_currNamespace_2620_ = lean_ctor_get(v_toCold_2614_, 4);
v_openDecls_2621_ = lean_ctor_get(v_toCold_2614_, 5);
v_quotContext_2622_ = lean_ctor_get(v_toCold_2614_, 8);
v_currMacroScope_2623_ = lean_ctor_get(v_toCold_2614_, 9);
v___f_2624_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2624_, 0, v_env_2615_);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2625_, 0, v_env_2615_);
lean_inc_n(v_openDecls_2621_, 2);
lean_inc_n(v_currNamespace_2620_, 3);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2626_, 0, v_env_2615_);
lean_closure_set(v___f_2626_, 1, v_currNamespace_2620_);
lean_closure_set(v___f_2626_, 2, v_openDecls_2621_);
v___f_2627_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2627_, 0, v_currNamespace_2620_);
lean_inc_ref(v_options_2618_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2628_, 0, v_env_2615_);
lean_closure_set(v___f_2628_, 1, v_options_2618_);
lean_closure_set(v___f_2628_, 2, v_currNamespace_2620_);
lean_closure_set(v___f_2628_, 3, v_openDecls_2621_);
v_methods_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2629_, 0, v___f_2624_);
lean_ctor_set(v_methods_2629_, 1, v___f_2627_);
lean_ctor_set(v_methods_2629_, 2, v___f_2625_);
lean_ctor_set(v_methods_2629_, 3, v___f_2626_);
lean_ctor_set(v_methods_2629_, 4, v___f_2628_);
v___x_2630_ = lean_st_ref_get(v___y_2611_);
v_nextMacroScope_2631_ = lean_ctor_get(v___x_2630_, 1);
lean_inc(v_nextMacroScope_2631_);
lean_dec(v___x_2630_);
lean_inc(v_ref_2617_);
lean_inc(v_maxRecDepth_2619_);
lean_inc(v_currRecDepth_2616_);
lean_inc(v_currMacroScope_2623_);
lean_inc(v_quotContext_2622_);
v___x_2632_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2632_, 0, v_methods_2629_);
lean_ctor_set(v___x_2632_, 1, v_quotContext_2622_);
lean_ctor_set(v___x_2632_, 2, v_currMacroScope_2623_);
lean_ctor_set(v___x_2632_, 3, v_currRecDepth_2616_);
lean_ctor_set(v___x_2632_, 4, v_maxRecDepth_2619_);
lean_ctor_set(v___x_2632_, 5, v_ref_2617_);
v___x_2633_ = lean_box(0);
v___x_2634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2634_, 0, v_nextMacroScope_2631_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
lean_ctor_set(v___x_2634_, 2, v___x_2633_);
v___x_2635_ = lean_apply_2(v_x_2605_, v___x_2632_, v___x_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v_a_2637_; lean_object* v_macroScope_2638_; lean_object* v_traceMsgs_2639_; lean_object* v_expandedMacroDecls_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 1);
lean_inc(v_a_2636_);
v_a_2637_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2635_, 2);
v_macroScope_2638_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_macroScope_2638_);
v_traceMsgs_2639_ = lean_ctor_get(v_a_2636_, 1);
lean_inc(v_traceMsgs_2639_);
v_expandedMacroDecls_2640_ = lean_ctor_get(v_a_2636_, 2);
lean_inc(v_expandedMacroDecls_2640_);
lean_dec(v_a_2636_);
v___x_2641_ = lean_box(0);
v___x_2642_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2640_, v___x_2641_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v_expandedMacroDecls_2640_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v___x_2643_; lean_object* v_env_2644_; lean_object* v_ngen_2645_; lean_object* v_auxDeclNGen_2646_; lean_object* v_traceState_2647_; lean_object* v_cache_2648_; lean_object* v_messages_2649_; lean_object* v_infoState_2650_; lean_object* v_snapshotTasks_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2677_; 
lean_dec_ref_known(v___x_2642_, 1);
v___x_2643_ = lean_st_ref_take(v___y_2611_);
v_env_2644_ = lean_ctor_get(v___x_2643_, 0);
v_ngen_2645_ = lean_ctor_get(v___x_2643_, 2);
v_auxDeclNGen_2646_ = lean_ctor_get(v___x_2643_, 3);
v_traceState_2647_ = lean_ctor_get(v___x_2643_, 4);
v_cache_2648_ = lean_ctor_get(v___x_2643_, 5);
v_messages_2649_ = lean_ctor_get(v___x_2643_, 6);
v_infoState_2650_ = lean_ctor_get(v___x_2643_, 7);
v_snapshotTasks_2651_ = lean_ctor_get(v___x_2643_, 8);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v___x_2643_, 1);
lean_dec(v_unused_2678_);
v___x_2653_ = v___x_2643_;
v_isShared_2654_ = v_isSharedCheck_2677_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_snapshotTasks_2651_);
lean_inc(v_infoState_2650_);
lean_inc(v_messages_2649_);
lean_inc(v_cache_2648_);
lean_inc(v_traceState_2647_);
lean_inc(v_auxDeclNGen_2646_);
lean_inc(v_ngen_2645_);
lean_inc(v_env_2644_);
lean_dec(v___x_2643_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2677_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v_macroScope_2638_);
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_env_2644_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_macroScope_2638_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_ngen_2645_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v_auxDeclNGen_2646_);
lean_ctor_set(v_reuseFailAlloc_2676_, 4, v_traceState_2647_);
lean_ctor_set(v_reuseFailAlloc_2676_, 5, v_cache_2648_);
lean_ctor_set(v_reuseFailAlloc_2676_, 6, v_messages_2649_);
lean_ctor_set(v_reuseFailAlloc_2676_, 7, v_infoState_2650_);
lean_ctor_set(v_reuseFailAlloc_2676_, 8, v_snapshotTasks_2651_);
v___x_2656_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_st_ref_put(v___y_2611_, v___x_2656_);
v___x_2658_ = l_List_reverse___redArg(v_traceMsgs_2639_);
v___x_2659_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2658_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2667_);
v___x_2661_ = v___x_2659_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2659_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_a_2637_);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2637_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2637_);
v_a_2668_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2659_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2659_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_traceMsgs_2639_);
lean_dec(v_macroScope_2638_);
lean_dec(v_a_2637_);
v_a_2679_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2642_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2642_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2635_, 2);
if (lean_obj_tag(v_a_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v_a_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v_a_2688_ = lean_ctor_get(v_a_2687_, 0);
lean_inc(v_a_2688_);
v_a_2689_ = lean_ctor_get(v_a_2687_, 1);
lean_inc_ref(v_a_2689_);
lean_dec_ref_known(v_a_2687_, 2);
v___x_2690_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2691_ = lean_string_dec_eq(v_a_2689_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_a_2689_);
v___x_2693_ = l_Lean_MessageData_ofFormat(v___x_2692_);
v___x_2694_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2688_, v___x_2693_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v_a_2688_);
return v___x_2694_;
}
else
{
lean_object* v___x_2695_; 
lean_dec_ref(v_a_2689_);
v___x_2695_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2688_);
return v___x_2695_;
}
}
else
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2705_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_box(0);
v___x_2707_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2708_ = l_Lean_mkConst(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2722_ = l_Lean_mkConst(v___x_2721_, v___x_2720_);
return v___x_2722_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2725_, lean_object* v_as_2726_, size_t v_sz_2727_, size_t v_i_2728_, lean_object* v_b_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_a_2738_; uint8_t v___x_2742_; 
v___x_2742_ = lean_usize_dec_lt(v_i_2728_, v_sz_2727_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_b_2729_);
return v___x_2743_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v_a_2746_; uint8_t v___x_2747_; 
v___x_2744_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2745_ = lean_box(0);
v_a_2746_ = lean_array_uget_borrowed(v_as_2726_, v_i_2728_);
lean_inc(v_a_2746_);
v___x_2747_ = l_Lean_Syntax_isOfKind(v_a_2746_, v___x_2744_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_dec_ref_known(v___x_2748_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2748_;
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = lean_unsigned_to_nat(1u);
v___x_2751_ = l_Lean_Syntax_getArg(v_a_2746_, v___x_2749_);
v___x_2752_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2751_);
v___x_2753_ = l_Lean_Syntax_isOfKind(v___x_2751_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2751_);
v___x_2755_ = l_Lean_Syntax_isOfKind(v___x_2751_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; 
lean_dec(v___x_2751_);
v___x_2756_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_dec_ref_known(v___x_2756_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2756_;
}
}
else
{
lean_object* v___x_2757_; uint8_t v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint64_t v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___x_2779_; lean_object* v___y_2781_; 
v___x_2757_ = lean_box(0);
v___x_2779_ = l_Lean_Syntax_getArg(v___x_2751_, v___x_2749_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2779_);
v___x_2853_ = l_Lean_Syntax_isOfKind(v___x_2779_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec(v___x_2779_);
lean_dec(v___x_2751_);
v___x_2854_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_dec_ref_known(v___x_2854_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2854_;
}
}
else
{
goto v___jp_2847_;
}
}
else
{
goto v___jp_2847_;
}
v___jp_2758_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2769_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0);
lean_inc_n(v___y_2760_, 2);
v___x_2770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2770_, 0, v___y_2760_);
lean_ctor_set(v___x_2770_, 1, v___x_2757_);
lean_ctor_set(v___x_2770_, 2, v___x_2769_);
v___x_2771_ = lean_box(0);
v___x_2772_ = 1;
v___x_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___y_2760_);
lean_ctor_set(v___x_2773_, 1, v___x_2757_);
v___x_2774_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2770_);
lean_ctor_set(v___x_2774_, 1, v___y_2761_);
lean_ctor_set(v___x_2774_, 2, v___x_2771_);
lean_ctor_set(v___x_2774_, 3, v___x_2773_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*4, v___x_2772_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
v___x_2776_ = l_Lean_addAndCompile(v___x_2775_, v___x_2725_, v___x_2753_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref_known(v___x_2776_, 1);
if (v___y_2759_ == 0)
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v___y_2762_, v___y_2760_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_dec_ref_known(v___x_2777_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2777_;
}
}
else
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v___y_2762_, v___y_2760_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_dec_ref_known(v___x_2778_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2778_;
}
}
}
else
{
lean_dec(v___y_2760_);
return v___x_2776_;
}
}
v___jp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2782_, 0, v___x_2779_);
v___x_2783_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2782_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = l_Lean_Widget_elabWidgetInstanceSpec(v___y_2781_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_n(v_a_2786_, 2);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2786_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2787_) == 0)
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_unbox(v_a_2784_);
if (v___x_2788_ == 1)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
v_a_2789_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2790_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2789_, v___y_2733_, v___y_2735_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_dec_ref_known(v___x_2790_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2790_;
}
}
else
{
lean_object* v_a_2791_; lean_object* v_id_2792_; uint64_t v_javascriptHash_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2791_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2787_, 1);
v_id_2792_ = lean_ctor_get(v_a_2791_, 0);
lean_inc(v_id_2792_);
v_javascriptHash_2793_ = lean_ctor_get_uint64(v_a_2791_, sizeof(void*)*2);
lean_dec(v_a_2791_);
v___x_2794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2));
v___x_2795_ = l_Lean_Name_append(v_id_2792_, v___x_2794_);
v___x_2796_ = l_Lean_Core_mkFreshUserName(v___x_2795_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2786_, v___y_2733_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; uint8_t v___x_2800_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = l_Lean_Expr_hasMVar(v_a_2799_);
if (v___x_2800_ == 0)
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_unbox(v_a_2784_);
lean_dec(v_a_2784_);
v___y_2759_ = v___x_2801_;
v___y_2760_ = v_a_2797_;
v___y_2761_ = v_a_2799_;
v___y_2762_ = v_javascriptHash_2793_;
v___y_2763_ = v___y_2730_;
v___y_2764_ = v___y_2731_;
v___y_2765_ = v___y_2732_;
v___y_2766_ = v___y_2733_;
v___y_2767_ = v___y_2734_;
v___y_2768_ = v___y_2735_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2799_);
v___x_2803_ = l_Lean_indentExpr(v_a_2799_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2804_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2805_) == 0)
{
uint8_t v___x_2806_; 
lean_dec_ref_known(v___x_2805_, 1);
v___x_2806_ = lean_unbox(v_a_2784_);
lean_dec(v_a_2784_);
v___y_2759_ = v___x_2806_;
v___y_2760_ = v_a_2797_;
v___y_2761_ = v_a_2799_;
v___y_2762_ = v_javascriptHash_2793_;
v___y_2763_ = v___y_2730_;
v___y_2764_ = v___y_2731_;
v___y_2765_ = v___y_2732_;
v___y_2766_ = v___y_2733_;
v___y_2767_ = v___y_2734_;
v___y_2768_ = v___y_2735_;
goto v___jp_2758_;
}
else
{
lean_dec(v_a_2799_);
lean_dec(v_a_2797_);
lean_dec(v_a_2784_);
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2797_);
lean_dec(v_a_2784_);
v_a_2807_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2798_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2798_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
v_a_2815_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2796_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2796_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
v_a_2823_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2787_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2787_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_a_2784_);
v_a_2831_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2785_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2785_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v___y_2781_);
v_a_2839_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2783_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2783_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
v___jp_2847_:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_Syntax_getArg(v___x_2751_, v___x_2750_);
lean_dec(v___x_2751_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2848_);
v___x_2850_ = l_Lean_Syntax_isOfKind(v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec(v___x_2848_);
lean_dec(v___x_2779_);
v___x_2851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2851_;
}
}
else
{
v___y_2781_ = v___x_2848_;
goto v___jp_2780_;
}
}
else
{
v___y_2781_ = v___x_2848_;
goto v___jp_2780_;
}
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2855_ = l_Lean_Syntax_getArg(v___x_2751_, v___x_2750_);
lean_dec(v___x_2751_);
v___x_2856_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2855_);
v___x_2857_ = l_Lean_Syntax_isOfKind(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec(v___x_2855_);
v___x_2858_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_dec_ref_known(v___x_2858_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2858_;
}
}
else
{
lean_object* v_toCold_2859_; lean_object* v_ref_2860_; lean_object* v_quotContext_2861_; lean_object* v_currMacroScope_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_toCold_2859_ = lean_ctor_get(v___y_2734_, 0);
v_ref_2860_ = lean_ctor_get(v___y_2734_, 2);
v_quotContext_2861_ = lean_ctor_get(v_toCold_2859_, 8);
v_currMacroScope_2862_ = lean_ctor_get(v_toCold_2859_, 9);
v___x_2863_ = 0;
v___x_2864_ = l_Lean_SourceInfo_fromRef(v_ref_2860_, v___x_2863_);
v___x_2865_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2866_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2867_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2862_);
lean_inc(v_quotContext_2861_);
v___x_2868_ = l_Lean_addMacroScope(v_quotContext_2861_, v___x_2867_, v_currMacroScope_2862_);
v___x_2869_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2864_, 2);
v___x_2870_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2864_);
lean_ctor_set(v___x_2870_, 1, v___x_2866_);
lean_ctor_set(v___x_2870_, 2, v___x_2868_);
lean_ctor_set(v___x_2870_, 3, v___x_2869_);
v___x_2871_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2872_ = l_Lean_Syntax_node1(v___x_2864_, v___x_2871_, v___x_2855_);
v___x_2873_ = l_Lean_Syntax_node2(v___x_2864_, v___x_2865_, v___x_2870_, v___x_2872_);
v___x_2874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2875_ = l_Lean_Elab_Term_elabTerm(v___x_2873_, v___x_2874_, v___x_2725_, v___x_2725_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2876_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; uint64_t v_javascriptHash_2879_; lean_object* v___x_2880_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v_javascriptHash_2879_ = lean_ctor_get_uint64(v_a_2878_, sizeof(void*)*1);
lean_dec(v_a_2878_);
v___x_2880_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2879_, v___y_2733_, v___y_2735_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_dec_ref_known(v___x_2880_, 1);
v_a_2738_ = v___x_2745_;
goto v___jp_2737_;
}
else
{
return v___x_2880_;
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
v_a_2881_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2877_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2877_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2875_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2875_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
}
v___jp_2737_:
{
size_t v___x_2739_; size_t v___x_2740_; 
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2728_, v___x_2739_);
v_i_2728_ = v___x_2740_;
v_b_2729_ = v_a_2738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2897_, lean_object* v_as_2898_, lean_object* v_sz_2899_, lean_object* v_i_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
uint8_t v___x_30388__boxed_2909_; size_t v_sz_boxed_2910_; size_t v_i_boxed_2911_; lean_object* v_res_2912_; 
v___x_30388__boxed_2909_ = lean_unbox(v___x_2897_);
v_sz_boxed_2910_ = lean_unbox_usize(v_sz_2899_);
lean_dec(v_sz_2899_);
v_i_boxed_2911_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_30388__boxed_2909_, v_as_2898_, v_sz_boxed_2910_, v_i_boxed_2911_, v_b_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v_as_2898_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2913_, lean_object* v___x_2914_, size_t v_sz_2915_, size_t v___x_2916_, lean_object* v___x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2913_, v___x_2914_, v_sz_2915_, v___x_2916_, v___x_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2925_, 0);
lean_dec(v_unused_2933_);
v___x_2927_ = v___x_2925_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_dec(v___x_2925_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2917_);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2917_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_2934_, lean_object* v___x_2935_, lean_object* v_sz_2936_, lean_object* v___x_2937_, lean_object* v___x_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v___x_30756__boxed_2946_; size_t v_sz_boxed_2947_; size_t v___x_30758__boxed_2948_; lean_object* v_res_2949_; 
v___x_30756__boxed_2946_ = lean_unbox(v___x_2934_);
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2936_);
lean_dec(v_sz_2936_);
v___x_30758__boxed_2948_ = lean_unbox_usize(v___x_2937_);
lean_dec(v___x_2937_);
v_res_2949_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_30756__boxed_2946_, v___x_2935_, v_sz_boxed_2947_, v___x_30758__boxed_2948_, v___x_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v___x_2935_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_2952_);
v___x_2957_ = l_Lean_Syntax_isOfKind(v_x_2952_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec(v_x_2952_);
v___x_2958_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_ws_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; size_t v_sz_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; 
v___x_2959_ = lean_unsigned_to_nat(2u);
v___x_2960_ = l_Lean_Syntax_getArg(v_x_2952_, v___x_2959_);
lean_dec(v_x_2952_);
v_ws_2961_ = l_Lean_Syntax_getArgs(v___x_2960_);
lean_dec(v___x_2960_);
v___x_2962_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_2961_);
lean_dec_ref(v_ws_2961_);
v___x_2963_ = lean_box(0);
v_sz_2964_ = lean_array_size(v___x_2962_);
v___x_2965_ = lean_box(v___x_2957_);
v___x_2966_ = lean_box_usize(v_sz_2964_);
v___x_2967_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2968_, 0, v___x_2965_);
lean_closure_set(v___f_2968_, 1, v___x_2962_);
lean_closure_set(v___f_2968_, 2, v___x_2966_);
lean_closure_set(v___f_2968_, 3, v___x_2967_);
lean_closure_set(v___f_2968_, 4, v___x_2963_);
v___x_2969_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2968_, v_a_2953_, v_a_2954_);
return v___x_2969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_2975_, lean_object* v_x_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2976_, v___y_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2980_, lean_object* v_x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_2980_, v_x_2981_, v___y_2982_, v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v_x_2981_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_2985_, lean_object* v_ref_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2986_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2995_, lean_object* v_ref_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_2995_, v_ref_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3005_, lean_object* v_x_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3015_, lean_object* v_x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3015_, v_x_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3025_, v___y_3029_, v___y_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object* v_00_u03b1_3043_, lean_object* v_00_u03b2_3044_, lean_object* v_00_u03c3_3045_, lean_object* v_ext_3046_, lean_object* v_b_3047_, uint8_t v_kind_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_3046_, v_b_3047_, v_kind_3048_, v___y_3052_, v___y_3053_, v___y_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object* v_00_u03b1_3057_, lean_object* v_00_u03b2_3058_, lean_object* v_00_u03c3_3059_, lean_object* v_ext_3060_, lean_object* v_b_3061_, lean_object* v_kind_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
uint8_t v_kind_boxed_3070_; lean_object* v_res_3071_; 
v_kind_boxed_3070_ = lean_unbox(v_kind_3062_);
v_res_3071_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_3057_, v_00_u03b2_3058_, v_00_u03c3_3059_, v_ext_3060_, v_b_3061_, v_kind_boxed_3070_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3072_, lean_object* v_msg_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3082_, lean_object* v_msg_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3082_, v_msg_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3092_, v___y_3096_, v___y_3098_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
uint64_t v_h_boxed_3109_; lean_object* v_res_3110_; 
v_h_boxed_3109_ = lean_unbox_uint64(v_h_3101_);
lean_dec_ref(v_h_3101_);
v_res_3110_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3109_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3111_, lean_object* v_msg_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3111_, v_msg_3112_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3121_, lean_object* v_msg_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3121_, v_msg_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3131_, lean_object* v_as_x27_3132_, lean_object* v_b_3133_, lean_object* v_a_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3132_, v_b_3133_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3143_, lean_object* v_as_x27_3144_, lean_object* v_b_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3143_, v_as_x27_3144_, v_b_3145_, v_a_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v_as_x27_3144_);
lean_dec(v_as_3143_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3155_, lean_object* v_ref_3156_, lean_object* v_msg_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3156_, v_msg_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_ref_3167_, lean_object* v_msg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3166_, v_ref_3167_, v_msg_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v_ref_3167_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3177_, lean_object* v_t_3178_, uint64_t v_k_3179_, lean_object* v_fallback_3180_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3178_, v_k_3179_, v_fallback_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3182_, lean_object* v_t_3183_, lean_object* v_k_3184_, lean_object* v_fallback_3185_){
_start:
{
uint64_t v_k_boxed_3186_; lean_object* v_res_3187_; 
v_k_boxed_3186_ = lean_unbox_uint64(v_k_3184_);
lean_dec_ref(v_k_3184_);
v_res_3187_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3182_, v_t_3183_, v_k_boxed_3186_, v_fallback_3185_);
lean_dec(v_fallback_3185_);
lean_dec(v_t_3183_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3188_, uint64_t v_k_3189_, lean_object* v_v_3190_, lean_object* v_t_3191_, lean_object* v_hl_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3189_, v_v_3190_, v_t_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3194_, lean_object* v_k_3195_, lean_object* v_v_3196_, lean_object* v_t_3197_, lean_object* v_hl_3198_){
_start:
{
uint64_t v_k_boxed_3199_; lean_object* v_res_3200_; 
v_k_boxed_3199_ = lean_unbox_uint64(v_k_3195_);
lean_dec_ref(v_k_3195_);
v_res_3200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3194_, v_k_boxed_3199_, v_v_3196_, v_t_3197_, v_hl_3198_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_3201_, lean_object* v_macroStack_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_3201_, v_macroStack_3202_, v___y_3207_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_3211_, lean_object* v_macroStack_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3211_, v_macroStack_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object* v_00_u03b2_3221_, uint64_t v_k_3222_, lean_object* v_t_3223_, lean_object* v_h_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3222_, v_t_3223_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object* v_00_u03b2_3226_, lean_object* v_k_3227_, lean_object* v_t_3228_, lean_object* v_h_3229_){
_start:
{
uint64_t v_k_boxed_3230_; lean_object* v_res_3231_; 
v_k_boxed_3230_ = lean_unbox_uint64(v_k_3227_);
lean_dec_ref(v_k_3227_);
v_res_3231_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_3226_, v_k_boxed_3230_, v_t_3228_, v_h_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3232_, lean_object* v_m_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3233_, v_a_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3236_, lean_object* v_m_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3236_, v_m_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_m_3237_);
return v_res_3239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object* v_00_u03b2_3240_, lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_3241_, v_x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object* v_00_u03b2_3244_, lean_object* v_x_3245_, lean_object* v_x_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_3244_, v_x_3245_, v_x_3246_);
lean_dec_ref(v_x_3246_);
lean_dec_ref(v_x_3245_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object* v_00_u03b2_3249_, lean_object* v_a_3250_, lean_object* v_x_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_3250_, v_x_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object* v_00_u03b2_3253_, lean_object* v_a_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_3253_, v_a_3254_, v_x_3255_);
lean_dec(v_x_3255_);
lean_dec(v_a_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object* v_00_u03b2_3257_, lean_object* v_x_3258_, size_t v_x_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_3258_, v_x_3259_, v_x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object* v_00_u03b2_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
size_t v_x_31120__boxed_3266_; uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_x_31120__boxed_3266_ = lean_unbox_usize(v_x_3264_);
lean_dec(v_x_3264_);
v_res_3267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_3262_, v_x_3263_, v_x_31120__boxed_3266_, v_x_3265_);
lean_dec_ref(v_x_3265_);
lean_dec_ref(v_x_3263_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object* v_00_u03b2_3269_, lean_object* v_keys_3270_, lean_object* v_vals_3271_, lean_object* v_heq_3272_, lean_object* v_i_3273_, lean_object* v_k_3274_){
_start:
{
uint8_t v___x_3275_; 
v___x_3275_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_3270_, v_i_3273_, v_k_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object* v_00_u03b2_3276_, lean_object* v_keys_3277_, lean_object* v_vals_3278_, lean_object* v_heq_3279_, lean_object* v_i_3280_, lean_object* v_k_3281_){
_start:
{
uint8_t v_res_3282_; lean_object* v_r_3283_; 
v_res_3282_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_3276_, v_keys_3277_, v_vals_3278_, v_heq_3279_, v_i_3280_, v_k_3281_);
lean_dec_ref(v_k_3281_);
lean_dec_ref(v_vals_3278_);
lean_dec_ref(v_keys_3277_);
v_r_3283_ = lean_box(v_res_3282_);
return v_r_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3301_, lean_object* v_x_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3301_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v___x_3312_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3311_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; uint64_t v_javascriptHash_3314_; lean_object* v_props_3315_; lean_object* v___x_3316_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v_javascriptHash_3314_ = lean_ctor_get_uint64(v_a_3313_, sizeof(void*)*2);
v_props_3315_ = lean_ctor_get(v_a_3313_, 1);
lean_inc_ref(v_props_3315_);
lean_dec(v_a_3313_);
v___x_3316_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3314_, v_props_3315_, v_x_3302_, v___y_3307_, v___y_3308_);
return v___x_3316_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_x_3302_);
v_a_3317_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3312_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3312_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_x_3302_);
v_a_3325_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3310_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3310_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3333_, lean_object* v_x_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3333_, v_x_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3343_);
v___x_3348_ = l_Lean_Syntax_isOfKind(v_x_3343_, v___x_3347_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_x_3343_);
v___x_3349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3349_;
}
else
{
lean_object* v___x_3350_; lean_object* v_s_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; 
v___x_3350_ = lean_unsigned_to_nat(1u);
v_s_3351_ = l_Lean_Syntax_getArg(v_x_3343_, v___x_3350_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3352_, 0, v_s_3351_);
lean_closure_set(v___f_3352_, 1, v_x_3343_);
v___x_3353_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3352_, v_a_3344_, v_a_3345_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Widget_elabWidgetCmd(v_x_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
return v_res_3358_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_Commands(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Widget_Commands(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_Commands(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Widget_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Widget_Commands(builtin);
}
#ifdef __cplusplus
}
#endif
