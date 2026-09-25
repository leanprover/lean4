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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_1297_; lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v_env_1300_; lean_object* v_nextMacroScope_1301_; lean_object* v_ngen_1302_; lean_object* v_auxDeclNGen_1303_; lean_object* v_traceState_1304_; lean_object* v_recordedDeps_1305_; lean_object* v_messages_1306_; lean_object* v_infoState_1307_; lean_object* v_snapshotTasks_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1336_; 
v___x_1297_ = lean_box_uint64(v_h_1293_);
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1298_, 0, v___x_1297_);
v___x_1299_ = lean_st_ref_take(v___y_1295_);
v_env_1300_ = lean_ctor_get(v___x_1299_, 0);
v_nextMacroScope_1301_ = lean_ctor_get(v___x_1299_, 1);
v_ngen_1302_ = lean_ctor_get(v___x_1299_, 2);
v_auxDeclNGen_1303_ = lean_ctor_get(v___x_1299_, 3);
v_traceState_1304_ = lean_ctor_get(v___x_1299_, 4);
v_recordedDeps_1305_ = lean_ctor_get(v___x_1299_, 6);
v_messages_1306_ = lean_ctor_get(v___x_1299_, 7);
v_infoState_1307_ = lean_ctor_get(v___x_1299_, 8);
v_snapshotTasks_1308_ = lean_ctor_get(v___x_1299_, 9);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1299_, 5);
lean_dec(v_unused_1337_);
v___x_1310_ = v___x_1299_;
v_isShared_1311_ = v_isSharedCheck_1336_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_snapshotTasks_1308_);
lean_inc(v_infoState_1307_);
lean_inc(v_messages_1306_);
lean_inc(v_recordedDeps_1305_);
lean_inc(v_traceState_1304_);
lean_inc(v_auxDeclNGen_1303_);
lean_inc(v_ngen_1302_);
lean_inc(v_nextMacroScope_1301_);
lean_inc(v_env_1300_);
lean_dec(v___x_1299_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1336_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1312_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1313_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1312_, v_env_1300_, v___f_1298_);
v___x_1314_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 5, v___x_1314_);
lean_ctor_set(v___x_1310_, 0, v___x_1313_);
v___x_1316_ = v___x_1310_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_nextMacroScope_1301_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_ngen_1302_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_auxDeclNGen_1303_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_traceState_1304_);
lean_ctor_set(v_reuseFailAlloc_1335_, 5, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1335_, 6, v_recordedDeps_1305_);
lean_ctor_set(v_reuseFailAlloc_1335_, 7, v_messages_1306_);
lean_ctor_set(v_reuseFailAlloc_1335_, 8, v_infoState_1307_);
lean_ctor_set(v_reuseFailAlloc_1335_, 9, v_snapshotTasks_1308_);
v___x_1316_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_mctx_1319_; lean_object* v_zetaDeltaFVarIds_1320_; lean_object* v_postponed_1321_; lean_object* v_diag_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1333_; 
v___x_1317_ = lean_st_ref_put(v___y_1295_, v___x_1316_);
v___x_1318_ = lean_st_ref_take(v___y_1294_);
v_mctx_1319_ = lean_ctor_get(v___x_1318_, 0);
v_zetaDeltaFVarIds_1320_ = lean_ctor_get(v___x_1318_, 2);
v_postponed_1321_ = lean_ctor_get(v___x_1318_, 3);
v_diag_1322_ = lean_ctor_get(v___x_1318_, 4);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v___x_1318_, 1);
lean_dec(v_unused_1334_);
v___x_1324_ = v___x_1318_;
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_diag_1322_);
lean_inc(v_postponed_1321_);
lean_inc(v_zetaDeltaFVarIds_1320_);
lean_inc(v_mctx_1319_);
lean_dec(v___x_1318_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1327_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_mctx_1319_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_zetaDeltaFVarIds_1320_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_postponed_1321_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_diag_1322_);
v___x_1329_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_st_ref_put(v___y_1294_, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1326_);
return v___x_1331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint64_t v_h_boxed_1342_; lean_object* v_res_1343_; 
v_h_boxed_1342_ = lean_unbox_uint64(v_h_1338_);
lean_dec_ref(v_h_1338_);
v_res_1343_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1342_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1344_, uint64_t v_k_1345_, lean_object* v_fallback_1346_){
_start:
{
if (lean_obj_tag(v_t_1344_) == 0)
{
lean_object* v_k_1347_; lean_object* v_v_1348_; lean_object* v_l_1349_; lean_object* v_r_1350_; uint64_t v___x_1351_; uint8_t v___x_1352_; 
v_k_1347_ = lean_ctor_get(v_t_1344_, 1);
v_v_1348_ = lean_ctor_get(v_t_1344_, 2);
v_l_1349_ = lean_ctor_get(v_t_1344_, 3);
v_r_1350_ = lean_ctor_get(v_t_1344_, 4);
v___x_1351_ = lean_unbox_uint64(v_k_1347_);
v___x_1352_ = lean_uint64_dec_lt(v_k_1345_, v___x_1351_);
if (v___x_1352_ == 0)
{
uint64_t v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = lean_unbox_uint64(v_k_1347_);
v___x_1354_ = lean_uint64_dec_eq(v_k_1345_, v___x_1353_);
if (v___x_1354_ == 0)
{
v_t_1344_ = v_r_1350_;
goto _start;
}
else
{
lean_inc(v_v_1348_);
return v_v_1348_;
}
}
else
{
v_t_1344_ = v_l_1349_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1346_);
return v_fallback_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1357_, lean_object* v_k_1358_, lean_object* v_fallback_1359_){
_start:
{
uint64_t v_k_boxed_1360_; lean_object* v_res_1361_; 
v_k_boxed_1360_ = lean_unbox_uint64(v_k_1358_);
lean_dec_ref(v_k_1358_);
v_res_1361_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1357_, v_k_boxed_1360_, v_fallback_1359_);
lean_dec(v_fallback_1359_);
lean_dec(v_t_1357_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1362_, lean_object* v_v_1363_, lean_object* v_t_1364_){
_start:
{
if (lean_obj_tag(v_t_1364_) == 0)
{
lean_object* v_size_1365_; lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v_l_1368_; lean_object* v_r_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1653_; 
v_size_1365_ = lean_ctor_get(v_t_1364_, 0);
v_k_1366_ = lean_ctor_get(v_t_1364_, 1);
v_v_1367_ = lean_ctor_get(v_t_1364_, 2);
v_l_1368_ = lean_ctor_get(v_t_1364_, 3);
v_r_1369_ = lean_ctor_get(v_t_1364_, 4);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_t_1364_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1371_ = v_t_1364_;
v_isShared_1372_ = v_isSharedCheck_1653_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_r_1369_);
lean_inc(v_l_1368_);
lean_inc(v_v_1367_);
lean_inc(v_k_1366_);
lean_inc(v_size_1365_);
lean_dec(v_t_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1653_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint64_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_unbox_uint64(v_k_1366_);
v___x_1374_ = lean_uint64_dec_lt(v_k_1362_, v___x_1373_);
if (v___x_1374_ == 0)
{
uint64_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_unbox_uint64(v_k_1366_);
v___x_1376_ = lean_uint64_dec_eq(v_k_1362_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v_impl_1377_; lean_object* v___x_1378_; 
lean_dec(v_size_1365_);
v_impl_1377_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1362_, v_v_1363_, v_r_1369_);
v___x_1378_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1368_) == 0)
{
lean_object* v_size_1379_; lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_l_1383_; lean_object* v_r_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_size_1379_ = lean_ctor_get(v_l_1368_, 0);
v_size_1380_ = lean_ctor_get(v_impl_1377_, 0);
lean_inc(v_size_1380_);
v_k_1381_ = lean_ctor_get(v_impl_1377_, 1);
lean_inc(v_k_1381_);
v_v_1382_ = lean_ctor_get(v_impl_1377_, 2);
lean_inc(v_v_1382_);
v_l_1383_ = lean_ctor_get(v_impl_1377_, 3);
lean_inc(v_l_1383_);
v_r_1384_ = lean_ctor_get(v_impl_1377_, 4);
lean_inc(v_r_1384_);
v___x_1385_ = lean_unsigned_to_nat(3u);
v___x_1386_ = lean_nat_mul(v___x_1385_, v_size_1379_);
v___x_1387_ = lean_nat_dec_lt(v___x_1386_, v_size_1380_);
lean_dec(v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec(v_r_1384_);
lean_dec(v_l_1383_);
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
v___x_1388_ = lean_nat_add(v___x_1378_, v_size_1379_);
v___x_1389_ = lean_nat_add(v___x_1388_, v_size_1380_);
lean_dec(v_size_1380_);
lean_dec(v___x_1388_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_impl_1377_);
lean_ctor_set(v___x_1371_, 0, v___x_1389_);
v___x_1391_ = v___x_1371_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_impl_1377_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1456_; 
v_isSharedCheck_1456_ = !lean_is_exclusive(v_impl_1377_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1457_ = lean_ctor_get(v_impl_1377_, 4);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_impl_1377_, 3);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_impl_1377_, 2);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_impl_1377_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_impl_1377_, 0);
lean_dec(v_unused_1461_);
v___x_1394_ = v_impl_1377_;
v_isShared_1395_ = v_isSharedCheck_1456_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_impl_1377_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1456_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v_size_1396_; lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v_l_1399_; lean_object* v_r_1400_; lean_object* v_size_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_size_1396_ = lean_ctor_get(v_l_1383_, 0);
v_k_1397_ = lean_ctor_get(v_l_1383_, 1);
v_v_1398_ = lean_ctor_get(v_l_1383_, 2);
v_l_1399_ = lean_ctor_get(v_l_1383_, 3);
v_r_1400_ = lean_ctor_get(v_l_1383_, 4);
v_size_1401_ = lean_ctor_get(v_r_1384_, 0);
v___x_1402_ = lean_unsigned_to_nat(2u);
v___x_1403_ = lean_nat_mul(v___x_1402_, v_size_1401_);
v___x_1404_ = lean_nat_dec_lt(v_size_1396_, v___x_1403_);
lean_dec(v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1432_; 
lean_inc(v_r_1400_);
lean_inc(v_l_1399_);
lean_inc(v_v_1398_);
lean_inc(v_k_1397_);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_l_1383_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; 
v_unused_1433_ = lean_ctor_get(v_l_1383_, 4);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_l_1383_, 3);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_l_1383_, 2);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_l_1383_, 1);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_l_1383_, 0);
lean_dec(v_unused_1437_);
v___x_1406_ = v_l_1383_;
v_isShared_1407_ = v_isSharedCheck_1432_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_l_1383_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1432_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1422_; 
v___x_1408_ = lean_nat_add(v___x_1378_, v_size_1379_);
v___x_1409_ = lean_nat_add(v___x_1408_, v_size_1380_);
lean_dec(v_size_1380_);
if (lean_obj_tag(v_l_1399_) == 0)
{
lean_object* v_size_1430_; 
v_size_1430_ = lean_ctor_get(v_l_1399_, 0);
lean_inc(v_size_1430_);
v___y_1422_ = v_size_1430_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___y_1422_ = v___x_1431_;
goto v___jp_1421_;
}
v___jp_1410_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_nat_add(v___y_1411_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec(v___y_1411_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 4, v_r_1384_);
lean_ctor_set(v___x_1406_, 3, v_r_1400_);
lean_ctor_set(v___x_1406_, 2, v_v_1382_);
lean_ctor_set(v___x_1406_, 1, v_k_1381_);
lean_ctor_set(v___x_1406_, 0, v___x_1414_);
v___x_1416_ = v___x_1406_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_r_1400_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_r_1384_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v___x_1416_);
lean_ctor_set(v___x_1394_, 3, v___y_1412_);
lean_ctor_set(v___x_1394_, 2, v_v_1398_);
lean_ctor_set(v___x_1394_, 1, v_k_1397_);
lean_ctor_set(v___x_1394_, 0, v___x_1409_);
v___x_1418_ = v___x_1394_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v___y_1412_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
v___jp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_nat_add(v___x_1408_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec(v___x_1408_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_l_1399_);
lean_ctor_set(v___x_1371_, 0, v___x_1423_);
v___x_1425_ = v___x_1371_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_l_1399_);
v___x_1425_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_nat_add(v___x_1378_, v_size_1401_);
if (lean_obj_tag(v_r_1400_) == 0)
{
lean_object* v_size_1427_; 
v_size_1427_ = lean_ctor_get(v_r_1400_, 0);
lean_inc(v_size_1427_);
v___y_1411_ = v___x_1426_;
v___y_1412_ = v___x_1425_;
v___y_1413_ = v_size_1427_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___y_1411_ = v___x_1426_;
v___y_1412_ = v___x_1425_;
v___y_1413_ = v___x_1428_;
goto v___jp_1410_;
}
}
}
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_del_object(v___x_1371_);
v___x_1438_ = lean_nat_add(v___x_1378_, v_size_1379_);
v___x_1439_ = lean_nat_add(v___x_1438_, v_size_1380_);
lean_dec(v_size_1380_);
v___x_1440_ = lean_nat_add(v___x_1438_, v_size_1396_);
lean_dec(v___x_1438_);
lean_inc_ref(v_l_1368_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_l_1383_);
lean_ctor_set(v___x_1394_, 3, v_l_1368_);
lean_ctor_set(v___x_1394_, 2, v_v_1367_);
lean_ctor_set(v___x_1394_, 1, v_k_1366_);
lean_ctor_set(v___x_1394_, 0, v___x_1440_);
v___x_1442_ = v___x_1394_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_l_1383_);
v___x_1442_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v_l_1368_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; 
v_unused_1450_ = lean_ctor_get(v_l_1368_, 4);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1368_, 3);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1368_, 2);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_l_1368_, 1);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_l_1368_, 0);
lean_dec(v_unused_1454_);
v___x_1444_ = v_l_1368_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_l_1368_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 4, v_r_1384_);
lean_ctor_set(v___x_1444_, 3, v___x_1442_);
lean_ctor_set(v___x_1444_, 2, v_v_1382_);
lean_ctor_set(v___x_1444_, 1, v_k_1381_);
lean_ctor_set(v___x_1444_, 0, v___x_1439_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_r_1384_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1462_; 
v_l_1462_ = lean_ctor_get(v_impl_1377_, 3);
lean_inc(v_l_1462_);
if (lean_obj_tag(v_l_1462_) == 0)
{
lean_object* v_r_1463_; lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1488_; 
v_r_1463_ = lean_ctor_get(v_impl_1377_, 4);
v_k_1464_ = lean_ctor_get(v_impl_1377_, 1);
v_v_1465_ = lean_ctor_get(v_impl_1377_, 2);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_impl_1377_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; lean_object* v_unused_1490_; 
v_unused_1489_ = lean_ctor_get(v_impl_1377_, 3);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_impl_1377_, 0);
lean_dec(v_unused_1490_);
v___x_1467_ = v_impl_1377_;
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_r_1463_);
lean_inc(v_v_1465_);
lean_inc(v_k_1464_);
lean_dec(v_impl_1377_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1484_; 
v_k_1469_ = lean_ctor_get(v_l_1462_, 1);
v_v_1470_ = lean_ctor_get(v_l_1462_, 2);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_l_1462_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; 
v_unused_1485_ = lean_ctor_get(v_l_1462_, 4);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_l_1462_, 3);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_l_1462_, 0);
lean_dec(v_unused_1487_);
v___x_1472_ = v_l_1462_;
v_isShared_1473_ = v_isSharedCheck_1484_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
lean_dec(v_l_1462_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1484_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1463_, 2);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v_r_1463_);
lean_ctor_set(v___x_1472_, 3, v_r_1463_);
lean_ctor_set(v___x_1472_, 2, v_v_1367_);
lean_ctor_set(v___x_1472_, 1, v_k_1366_);
lean_ctor_set(v___x_1472_, 0, v___x_1378_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_r_1463_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_r_1463_);
v___x_1476_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
lean_inc(v_r_1463_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 3, v_r_1463_);
lean_ctor_set(v___x_1467_, 0, v___x_1378_);
v___x_1478_ = v___x_1467_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1464_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1465_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_r_1463_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_r_1463_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1478_);
lean_ctor_set(v___x_1371_, 3, v___x_1476_);
lean_ctor_set(v___x_1371_, 2, v_v_1470_);
lean_ctor_set(v___x_1371_, 1, v_k_1469_);
lean_ctor_set(v___x_1371_, 0, v___x_1474_);
v___x_1480_ = v___x_1371_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
else
{
lean_object* v_r_1491_; 
v_r_1491_ = lean_ctor_get(v_impl_1377_, 4);
lean_inc(v_r_1491_);
if (lean_obj_tag(v_r_1491_) == 0)
{
lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1504_; 
v_k_1492_ = lean_ctor_get(v_impl_1377_, 1);
v_v_1493_ = lean_ctor_get(v_impl_1377_, 2);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_impl_1377_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1505_ = lean_ctor_get(v_impl_1377_, 4);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_impl_1377_, 3);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_impl_1377_, 0);
lean_dec(v_unused_1507_);
v___x_1495_ = v_impl_1377_;
v_isShared_1496_ = v_isSharedCheck_1504_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_v_1493_);
lean_inc(v_k_1492_);
lean_dec(v_impl_1377_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1504_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_unsigned_to_nat(3u);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 4, v_l_1462_);
lean_ctor_set(v___x_1495_, 2, v_v_1367_);
lean_ctor_set(v___x_1495_, 1, v_k_1366_);
lean_ctor_set(v___x_1495_, 0, v___x_1378_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_l_1462_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_l_1462_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_r_1491_);
lean_ctor_set(v___x_1371_, 3, v___x_1499_);
lean_ctor_set(v___x_1371_, 2, v_v_1493_);
lean_ctor_set(v___x_1371_, 1, v_k_1492_);
lean_ctor_set(v___x_1371_, 0, v___x_1497_);
v___x_1501_ = v___x_1371_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1493_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_r_1491_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_unsigned_to_nat(2u);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_impl_1377_);
lean_ctor_set(v___x_1371_, 3, v_r_1491_);
lean_ctor_set(v___x_1371_, 0, v___x_1508_);
v___x_1510_ = v___x_1371_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_r_1491_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_impl_1377_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_dec(v_v_1367_);
lean_dec(v_k_1366_);
v___x_1512_ = lean_box_uint64(v_k_1362_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 2, v_v_1363_);
lean_ctor_set(v___x_1371_, 1, v___x_1512_);
v___x_1514_ = v___x_1371_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_size_1365_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1363_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_r_1369_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
lean_object* v_impl_1516_; lean_object* v___x_1517_; 
lean_dec(v_size_1365_);
v_impl_1516_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1362_, v_v_1363_, v_l_1368_);
v___x_1517_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1369_) == 0)
{
lean_object* v_size_1518_; lean_object* v_size_1519_; lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_l_1522_; lean_object* v_r_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v_size_1518_ = lean_ctor_get(v_r_1369_, 0);
v_size_1519_ = lean_ctor_get(v_impl_1516_, 0);
lean_inc(v_size_1519_);
v_k_1520_ = lean_ctor_get(v_impl_1516_, 1);
lean_inc(v_k_1520_);
v_v_1521_ = lean_ctor_get(v_impl_1516_, 2);
lean_inc(v_v_1521_);
v_l_1522_ = lean_ctor_get(v_impl_1516_, 3);
lean_inc(v_l_1522_);
v_r_1523_ = lean_ctor_get(v_impl_1516_, 4);
lean_inc(v_r_1523_);
v___x_1524_ = lean_unsigned_to_nat(3u);
v___x_1525_ = lean_nat_mul(v___x_1524_, v_size_1518_);
v___x_1526_ = lean_nat_dec_lt(v___x_1525_, v_size_1519_);
lean_dec(v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_dec(v_r_1523_);
lean_dec(v_l_1522_);
lean_dec(v_v_1521_);
lean_dec(v_k_1520_);
v___x_1527_ = lean_nat_add(v___x_1517_, v_size_1519_);
lean_dec(v_size_1519_);
v___x_1528_ = lean_nat_add(v___x_1527_, v_size_1518_);
lean_dec(v___x_1527_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 3, v_impl_1516_);
lean_ctor_set(v___x_1371_, 0, v___x_1528_);
v___x_1530_ = v___x_1371_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1369_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
else
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v_impl_1516_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1598_ = lean_ctor_get(v_impl_1516_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1516_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1516_, 2);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1516_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_impl_1516_, 0);
lean_dec(v_unused_1602_);
v___x_1533_ = v_impl_1516_;
v_isShared_1534_ = v_isSharedCheck_1597_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v_impl_1516_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1597_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_size_1535_; lean_object* v_size_1536_; lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v_l_1539_; lean_object* v_r_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_size_1535_ = lean_ctor_get(v_l_1522_, 0);
v_size_1536_ = lean_ctor_get(v_r_1523_, 0);
v_k_1537_ = lean_ctor_get(v_r_1523_, 1);
v_v_1538_ = lean_ctor_get(v_r_1523_, 2);
v_l_1539_ = lean_ctor_get(v_r_1523_, 3);
v_r_1540_ = lean_ctor_get(v_r_1523_, 4);
v___x_1541_ = lean_unsigned_to_nat(2u);
v___x_1542_ = lean_nat_mul(v___x_1541_, v_size_1535_);
v___x_1543_ = lean_nat_dec_lt(v_size_1536_, v___x_1542_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1572_; 
lean_inc(v_r_1540_);
lean_inc(v_l_1539_);
lean_inc(v_v_1538_);
lean_inc(v_k_1537_);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_r_1523_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1573_ = lean_ctor_get(v_r_1523_, 4);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_r_1523_, 3);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_r_1523_, 2);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_r_1523_, 1);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_r_1523_, 0);
lean_dec(v_unused_1577_);
v___x_1545_ = v_r_1523_;
v_isShared_1546_ = v_isSharedCheck_1572_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v_r_1523_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1572_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___x_1560_; lean_object* v___y_1562_; 
v___x_1547_ = lean_nat_add(v___x_1517_, v_size_1519_);
lean_dec(v_size_1519_);
v___x_1548_ = lean_nat_add(v___x_1547_, v_size_1518_);
lean_dec(v___x_1547_);
v___x_1560_ = lean_nat_add(v___x_1517_, v_size_1535_);
if (lean_obj_tag(v_l_1539_) == 0)
{
lean_object* v_size_1570_; 
v_size_1570_ = lean_ctor_get(v_l_1539_, 0);
lean_inc(v_size_1570_);
v___y_1562_ = v_size_1570_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
v___y_1562_ = v___x_1571_;
goto v___jp_1561_;
}
v___jp_1549_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = lean_nat_add(v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec(v___y_1551_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v_r_1369_);
lean_ctor_set(v___x_1545_, 3, v_r_1540_);
lean_ctor_set(v___x_1545_, 2, v_v_1367_);
lean_ctor_set(v___x_1545_, 1, v_k_1366_);
lean_ctor_set(v___x_1545_, 0, v___x_1553_);
v___x_1555_ = v___x_1545_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_r_1540_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1369_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v___x_1555_);
lean_ctor_set(v___x_1533_, 3, v___y_1550_);
lean_ctor_set(v___x_1533_, 2, v_v_1538_);
lean_ctor_set(v___x_1533_, 1, v_k_1537_);
lean_ctor_set(v___x_1533_, 0, v___x_1548_);
v___x_1557_ = v___x_1533_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___y_1550_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_nat_add(v___x_1560_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec(v___x_1560_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_l_1539_);
lean_ctor_set(v___x_1371_, 3, v_l_1522_);
lean_ctor_set(v___x_1371_, 2, v_v_1521_);
lean_ctor_set(v___x_1371_, 1, v_k_1520_);
lean_ctor_set(v___x_1371_, 0, v___x_1563_);
v___x_1565_ = v___x_1371_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_l_1522_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_l_1539_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_nat_add(v___x_1517_, v_size_1518_);
if (lean_obj_tag(v_r_1540_) == 0)
{
lean_object* v_size_1567_; 
v_size_1567_ = lean_ctor_get(v_r_1540_, 0);
lean_inc(v_size_1567_);
v___y_1550_ = v___x_1565_;
v___y_1551_ = v___x_1566_;
v___y_1552_ = v_size_1567_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___y_1550_ = v___x_1565_;
v___y_1551_ = v___x_1566_;
v___y_1552_ = v___x_1568_;
goto v___jp_1549_;
}
}
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_del_object(v___x_1371_);
v___x_1578_ = lean_nat_add(v___x_1517_, v_size_1519_);
lean_dec(v_size_1519_);
v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1518_);
lean_dec(v___x_1578_);
v___x_1580_ = lean_nat_add(v___x_1517_, v_size_1518_);
v___x_1581_ = lean_nat_add(v___x_1580_, v_size_1536_);
lean_dec(v___x_1580_);
lean_inc_ref(v_r_1369_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v_r_1369_);
lean_ctor_set(v___x_1533_, 3, v_r_1523_);
lean_ctor_set(v___x_1533_, 2, v_v_1367_);
lean_ctor_set(v___x_1533_, 1, v_k_1366_);
lean_ctor_set(v___x_1533_, 0, v___x_1581_);
v___x_1583_ = v___x_1533_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_r_1523_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_r_1369_);
v___x_1583_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v_r_1369_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1591_ = lean_ctor_get(v_r_1369_, 4);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_r_1369_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_r_1369_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_r_1369_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_r_1369_, 0);
lean_dec(v_unused_1595_);
v___x_1585_ = v_r_1369_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v_r_1369_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 4, v___x_1583_);
lean_ctor_set(v___x_1585_, 3, v_l_1522_);
lean_ctor_set(v___x_1585_, 2, v_v_1521_);
lean_ctor_set(v___x_1585_, 1, v_k_1520_);
lean_ctor_set(v___x_1585_, 0, v___x_1579_);
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_l_1522_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1603_; 
v_l_1603_ = lean_ctor_get(v_impl_1516_, 3);
lean_inc(v_l_1603_);
if (lean_obj_tag(v_l_1603_) == 0)
{
lean_object* v_r_1604_; lean_object* v_k_1605_; lean_object* v_v_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1617_; 
v_r_1604_ = lean_ctor_get(v_impl_1516_, 4);
v_k_1605_ = lean_ctor_get(v_impl_1516_, 1);
v_v_1606_ = lean_ctor_get(v_impl_1516_, 2);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_impl_1516_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; lean_object* v_unused_1619_; 
v_unused_1618_ = lean_ctor_get(v_impl_1516_, 3);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_impl_1516_, 0);
lean_dec(v_unused_1619_);
v___x_1608_ = v_impl_1516_;
v_isShared_1609_ = v_isSharedCheck_1617_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_r_1604_);
lean_inc(v_v_1606_);
lean_inc(v_k_1605_);
lean_dec(v_impl_1516_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1617_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1604_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v_r_1604_);
lean_ctor_set(v___x_1608_, 2, v_v_1367_);
lean_ctor_set(v___x_1608_, 1, v_k_1366_);
lean_ctor_set(v___x_1608_, 0, v___x_1517_);
v___x_1612_ = v___x_1608_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_r_1604_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_r_1604_);
v___x_1612_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1614_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1612_);
lean_ctor_set(v___x_1371_, 3, v_l_1603_);
lean_ctor_set(v___x_1371_, 2, v_v_1606_);
lean_ctor_set(v___x_1371_, 1, v_k_1605_);
lean_ctor_set(v___x_1371_, 0, v___x_1610_);
v___x_1614_ = v___x_1371_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1605_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1606_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_l_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_r_1620_; 
v_r_1620_ = lean_ctor_get(v_impl_1516_, 4);
lean_inc(v_r_1620_);
if (lean_obj_tag(v_r_1620_) == 0)
{
lean_object* v_k_1621_; lean_object* v_v_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1645_; 
v_k_1621_ = lean_ctor_get(v_impl_1516_, 1);
v_v_1622_ = lean_ctor_get(v_impl_1516_, 2);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_impl_1516_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1646_ = lean_ctor_get(v_impl_1516_, 4);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_impl_1516_, 3);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1516_, 0);
lean_dec(v_unused_1648_);
v___x_1624_ = v_impl_1516_;
v_isShared_1625_ = v_isSharedCheck_1645_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_v_1622_);
lean_inc(v_k_1621_);
lean_dec(v_impl_1516_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1645_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1641_; 
v_k_1626_ = lean_ctor_get(v_r_1620_, 1);
v_v_1627_ = lean_ctor_get(v_r_1620_, 2);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_r_1620_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; lean_object* v_unused_1643_; lean_object* v_unused_1644_; 
v_unused_1642_ = lean_ctor_get(v_r_1620_, 4);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_r_1620_, 3);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_r_1620_, 0);
lean_dec(v_unused_1644_);
v___x_1629_ = v_r_1620_;
v_isShared_1630_ = v_isSharedCheck_1641_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_v_1627_);
lean_inc(v_k_1626_);
lean_dec(v_r_1620_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1641_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_unsigned_to_nat(3u);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 4, v_l_1603_);
lean_ctor_set(v___x_1629_, 3, v_l_1603_);
lean_ctor_set(v___x_1629_, 2, v_v_1622_);
lean_ctor_set(v___x_1629_, 1, v_k_1621_);
lean_ctor_set(v___x_1629_, 0, v___x_1517_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1621_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1622_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_l_1603_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_l_1603_);
v___x_1633_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_l_1603_);
lean_ctor_set(v___x_1624_, 2, v_v_1367_);
lean_ctor_set(v___x_1624_, 1, v_k_1366_);
lean_ctor_set(v___x_1624_, 0, v___x_1517_);
v___x_1635_ = v___x_1624_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_l_1603_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_l_1603_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1635_);
lean_ctor_set(v___x_1371_, 3, v___x_1633_);
lean_ctor_set(v___x_1371_, 2, v_v_1627_);
lean_ctor_set(v___x_1371_, 1, v_k_1626_);
lean_ctor_set(v___x_1371_, 0, v___x_1631_);
v___x_1637_ = v___x_1371_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_unsigned_to_nat(2u);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_r_1620_);
lean_ctor_set(v___x_1371_, 3, v_impl_1516_);
lean_ctor_set(v___x_1371_, 0, v___x_1649_);
v___x_1651_ = v___x_1371_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_r_1620_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_box_uint64(v_k_1362_);
v___x_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
lean_ctor_set(v___x_1656_, 2, v_v_1363_);
lean_ctor_set(v___x_1656_, 3, v_t_1364_);
lean_ctor_set(v___x_1656_, 4, v_t_1364_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1657_, lean_object* v_v_1658_, lean_object* v_t_1659_){
_start:
{
uint64_t v_k_boxed_1660_; lean_object* v_res_1661_; 
v_k_boxed_1660_ = lean_unbox_uint64(v_k_1657_);
lean_dec_ref(v_k_1657_);
v_res_1661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1660_, v_v_1658_, v_t_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1662_, lean_object* v_s_1663_){
_start:
{
uint64_t v_javascriptHash_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_javascriptHash_1664_ = lean_ctor_get_uint64(v_wi_1662_, sizeof(void*)*2);
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_wi_1662_);
v___x_1666_ = lean_box(0);
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1663_, v_javascriptHash_1664_, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1665_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1664_, v___x_1668_, v_s_1663_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v_env_1676_; lean_object* v_nextMacroScope_1677_; lean_object* v_ngen_1678_; lean_object* v_auxDeclNGen_1679_; lean_object* v_traceState_1680_; lean_object* v_recordedDeps_1681_; lean_object* v_messages_1682_; lean_object* v_infoState_1683_; lean_object* v_snapshotTasks_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1712_; 
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1674_, 0, v_wi_1670_);
v___x_1675_ = lean_st_ref_take(v___y_1672_);
v_env_1676_ = lean_ctor_get(v___x_1675_, 0);
v_nextMacroScope_1677_ = lean_ctor_get(v___x_1675_, 1);
v_ngen_1678_ = lean_ctor_get(v___x_1675_, 2);
v_auxDeclNGen_1679_ = lean_ctor_get(v___x_1675_, 3);
v_traceState_1680_ = lean_ctor_get(v___x_1675_, 4);
v_recordedDeps_1681_ = lean_ctor_get(v___x_1675_, 6);
v_messages_1682_ = lean_ctor_get(v___x_1675_, 7);
v_infoState_1683_ = lean_ctor_get(v___x_1675_, 8);
v_snapshotTasks_1684_ = lean_ctor_get(v___x_1675_, 9);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v___x_1675_, 5);
lean_dec(v_unused_1713_);
v___x_1686_ = v___x_1675_;
v_isShared_1687_ = v_isSharedCheck_1712_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snapshotTasks_1684_);
lean_inc(v_infoState_1683_);
lean_inc(v_messages_1682_);
lean_inc(v_recordedDeps_1681_);
lean_inc(v_traceState_1680_);
lean_inc(v_auxDeclNGen_1679_);
lean_inc(v_ngen_1678_);
lean_inc(v_nextMacroScope_1677_);
lean_inc(v_env_1676_);
lean_dec(v___x_1675_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1712_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1688_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1689_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1688_, v_env_1676_, v___f_1674_);
v___x_1690_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 5, v___x_1690_);
lean_ctor_set(v___x_1686_, 0, v___x_1689_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_nextMacroScope_1677_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v_ngen_1678_);
lean_ctor_set(v_reuseFailAlloc_1711_, 3, v_auxDeclNGen_1679_);
lean_ctor_set(v_reuseFailAlloc_1711_, 4, v_traceState_1680_);
lean_ctor_set(v_reuseFailAlloc_1711_, 5, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1711_, 6, v_recordedDeps_1681_);
lean_ctor_set(v_reuseFailAlloc_1711_, 7, v_messages_1682_);
lean_ctor_set(v_reuseFailAlloc_1711_, 8, v_infoState_1683_);
lean_ctor_set(v_reuseFailAlloc_1711_, 9, v_snapshotTasks_1684_);
v___x_1692_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_mctx_1695_; lean_object* v_zetaDeltaFVarIds_1696_; lean_object* v_postponed_1697_; lean_object* v_diag_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1709_; 
v___x_1693_ = lean_st_ref_put(v___y_1672_, v___x_1692_);
v___x_1694_ = lean_st_ref_take(v___y_1671_);
v_mctx_1695_ = lean_ctor_get(v___x_1694_, 0);
v_zetaDeltaFVarIds_1696_ = lean_ctor_get(v___x_1694_, 2);
v_postponed_1697_ = lean_ctor_get(v___x_1694_, 3);
v_diag_1698_ = lean_ctor_get(v___x_1694_, 4);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v___x_1694_, 1);
lean_dec(v_unused_1710_);
v___x_1700_ = v___x_1694_;
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_diag_1698_);
lean_inc(v_postponed_1697_);
lean_inc(v_zetaDeltaFVarIds_1696_);
lean_inc(v_mctx_1695_);
lean_dec(v___x_1694_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1703_);
v___x_1705_ = v___x_1700_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_mctx_1695_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_zetaDeltaFVarIds_1696_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_postponed_1697_);
lean_ctor_set(v_reuseFailAlloc_1708_, 4, v_diag_1698_);
v___x_1705_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_st_ref_put(v___y_1671_, v___x_1705_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1702_);
return v___x_1707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec(v___y_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(lean_object* v_ext_1719_, lean_object* v_b_1720_, uint8_t v_kind_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_toCold_1726_; lean_object* v_currNamespace_1727_; lean_object* v___x_1728_; lean_object* v_env_1729_; lean_object* v_nextMacroScope_1730_; lean_object* v_ngen_1731_; lean_object* v_auxDeclNGen_1732_; lean_object* v_traceState_1733_; lean_object* v_recordedDeps_1734_; lean_object* v_messages_1735_; lean_object* v_infoState_1736_; lean_object* v_snapshotTasks_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1764_; 
v_toCold_1726_ = lean_ctor_get(v___y_1723_, 0);
v_currNamespace_1727_ = lean_ctor_get(v_toCold_1726_, 4);
v___x_1728_ = lean_st_ref_take(v___y_1724_);
v_env_1729_ = lean_ctor_get(v___x_1728_, 0);
v_nextMacroScope_1730_ = lean_ctor_get(v___x_1728_, 1);
v_ngen_1731_ = lean_ctor_get(v___x_1728_, 2);
v_auxDeclNGen_1732_ = lean_ctor_get(v___x_1728_, 3);
v_traceState_1733_ = lean_ctor_get(v___x_1728_, 4);
v_recordedDeps_1734_ = lean_ctor_get(v___x_1728_, 6);
v_messages_1735_ = lean_ctor_get(v___x_1728_, 7);
v_infoState_1736_ = lean_ctor_get(v___x_1728_, 8);
v_snapshotTasks_1737_ = lean_ctor_get(v___x_1728_, 9);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v___x_1728_, 5);
lean_dec(v_unused_1765_);
v___x_1739_ = v___x_1728_;
v_isShared_1740_ = v_isSharedCheck_1764_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_snapshotTasks_1737_);
lean_inc(v_infoState_1736_);
lean_inc(v_messages_1735_);
lean_inc(v_recordedDeps_1734_);
lean_inc(v_traceState_1733_);
lean_inc(v_auxDeclNGen_1732_);
lean_inc(v_ngen_1731_);
lean_inc(v_nextMacroScope_1730_);
lean_inc(v_env_1729_);
lean_dec(v___x_1728_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1764_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_inc(v_currNamespace_1727_);
v___x_1741_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1729_, v_ext_1719_, v_b_1720_, v_kind_1721_, v_currNamespace_1727_);
v___x_1742_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 5, v___x_1742_);
lean_ctor_set(v___x_1739_, 0, v___x_1741_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_nextMacroScope_1730_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_ngen_1731_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_auxDeclNGen_1732_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_traceState_1733_);
lean_ctor_set(v_reuseFailAlloc_1763_, 5, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1763_, 6, v_recordedDeps_1734_);
lean_ctor_set(v_reuseFailAlloc_1763_, 7, v_messages_1735_);
lean_ctor_set(v_reuseFailAlloc_1763_, 8, v_infoState_1736_);
lean_ctor_set(v_reuseFailAlloc_1763_, 9, v_snapshotTasks_1737_);
v___x_1744_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_mctx_1747_; lean_object* v_zetaDeltaFVarIds_1748_; lean_object* v_postponed_1749_; lean_object* v_diag_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1761_; 
v___x_1745_ = lean_st_ref_put(v___y_1724_, v___x_1744_);
v___x_1746_ = lean_st_ref_take(v___y_1722_);
v_mctx_1747_ = lean_ctor_get(v___x_1746_, 0);
v_zetaDeltaFVarIds_1748_ = lean_ctor_get(v___x_1746_, 2);
v_postponed_1749_ = lean_ctor_get(v___x_1746_, 3);
v_diag_1750_ = lean_ctor_get(v___x_1746_, 4);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1746_, 1);
lean_dec(v_unused_1762_);
v___x_1752_ = v___x_1746_;
v_isShared_1753_ = v_isSharedCheck_1761_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_diag_1750_);
lean_inc(v_postponed_1749_);
lean_inc(v_zetaDeltaFVarIds_1748_);
lean_inc(v_mctx_1747_);
lean_dec(v___x_1746_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1761_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_mctx_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_zetaDeltaFVarIds_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_postponed_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_diag_1750_);
v___x_1757_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_st_ref_put(v___y_1722_, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1754_);
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(lean_object* v_ext_1766_, lean_object* v_b_1767_, lean_object* v_kind_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_kind_boxed_1773_; lean_object* v_res_1774_; 
v_kind_boxed_1773_ = lean_unbox(v_kind_1768_);
v_res_1774_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_1766_, v_b_1767_, v_kind_boxed_1773_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1775_, lean_object* v_n_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1784_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1785_ = lean_box_uint64(v_h_1775_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v_n_1776_);
v___x_1787_ = 2;
v___x_1788_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1784_, v___x_1786_, v___x_1787_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1789_, lean_object* v_n_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint64_t v_h_boxed_1798_; lean_object* v_res_1799_; 
v_h_boxed_1798_ = lean_unbox_uint64(v_h_1789_);
lean_dec_ref(v_h_1789_);
v_res_1799_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1798_, v_n_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1800_, lean_object* v_n_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1809_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1810_ = lean_box_uint64(v_h_1800_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_n_1801_);
v___x_1812_ = 0;
v___x_1813_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1809_, v___x_1811_, v___x_1812_, v___y_1805_, v___y_1806_, v___y_1807_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1814_, lean_object* v_n_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint64_t v_h_boxed_1823_; lean_object* v_res_1824_; 
v_h_boxed_1823_ = lean_unbox_uint64(v_h_1814_);
lean_dec_ref(v_h_1814_);
v_res_1824_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1823_, v_n_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_1825_, lean_object* v___y_1826_){
_start:
{
if (lean_obj_tag(v_x_1825_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v_x_1825_, 0);
lean_inc(v_a_1827_);
v___x_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1827_);
lean_ctor_set(v___x_1828_, 1, v___y_1826_);
return v___x_1828_;
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v_x_1825_, 0);
lean_inc(v_a_1829_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1829_);
lean_ctor_set(v___x_1830_, 1, v___y_1826_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_1831_, v___y_1832_);
lean_dec_ref(v_x_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1834_, lean_object* v_stx_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1834_, v_stx_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
if (lean_obj_tag(v_a_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
v_a_1840_ = lean_ctor_get(v___x_1838_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1838_, 0);
lean_dec(v_unused_1849_);
v___x_1842_ = v___x_1838_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1838_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_a_1840_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1878_; 
v_val_1850_ = lean_ctor_get(v_a_1839_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1852_ = v_a_1839_;
v_isShared_1853_ = v_isSharedCheck_1878_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_val_1850_);
lean_dec(v_a_1839_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1878_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_snd_1854_; 
v_snd_1854_ = lean_ctor_get(v_val_1850_, 1);
lean_inc(v_snd_1854_);
lean_dec(v_val_1850_);
if (lean_obj_tag(v_snd_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
lean_del_object(v___x_1852_);
v_a_1855_ = lean_ctor_get(v___x_1838_, 1);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1838_, 2);
v_a_1856_ = lean_ctor_get(v_snd_1854_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_snd_1854_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v_snd_1854_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v_snd_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1861_, v_a_1855_);
lean_dec_ref(v___x_1861_);
return v___x_1862_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1877_; 
v_a_1865_ = lean_ctor_get(v___x_1838_, 1);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1838_, 2);
v_a_1866_ = lean_ctor_get(v_snd_1854_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_snd_1854_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1868_ = v_snd_1854_;
v_isShared_1869_ = v_isSharedCheck_1877_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v_snd_1854_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1877_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_a_1866_);
v___x_1871_ = v___x_1852_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1871_);
v___x_1873_ = v___x_1868_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1873_, v_a_1865_);
lean_dec_ref(v___x_1873_);
return v___x_1874_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1879_ = lean_ctor_get(v___x_1838_, 0);
v_a_1880_ = lean_ctor_get(v___x_1838_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1838_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_inc(v_a_1879_);
lean_dec(v___x_1838_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1879_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1888_, lean_object* v_stx_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1888_, v_stx_1889_, v___y_1890_, v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(lean_object* v_msgData_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v_env_1900_; lean_object* v___x_1901_; lean_object* v_toCold_1902_; lean_object* v_mctx_1903_; lean_object* v_lctx_1904_; lean_object* v_options_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1899_ = lean_st_ref_get(v___y_1897_);
v_env_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc_ref(v_env_1900_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_st_ref_get(v___y_1895_);
v_toCold_1902_ = lean_ctor_get(v___y_1896_, 0);
v_mctx_1903_ = lean_ctor_get(v___x_1901_, 0);
lean_inc_ref(v_mctx_1903_);
lean_dec(v___x_1901_);
v_lctx_1904_ = lean_ctor_get(v___y_1894_, 2);
v_options_1905_ = lean_ctor_get(v_toCold_1902_, 2);
lean_inc_ref(v_options_1905_);
lean_inc_ref(v_lctx_1904_);
v___x_1906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1906_, 0, v_env_1900_);
lean_ctor_set(v___x_1906_, 1, v_mctx_1903_);
lean_ctor_set(v___x_1906_, 2, v_lctx_1904_);
lean_ctor_set(v___x_1906_, 3, v_options_1905_);
v___x_1907_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v_msgData_1893_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object* v_msgData_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1915_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1916_; double v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(0u);
v___x_1917_ = lean_float_of_nat(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1920_, lean_object* v_msg_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_ref_1927_; lean_object* v___x_1928_; lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1974_; 
v_ref_1927_ = lean_ctor_get(v___y_1924_, 2);
v___x_1928_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1974_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1974_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v_traceState_1934_; lean_object* v_env_1935_; lean_object* v_nextMacroScope_1936_; lean_object* v_ngen_1937_; lean_object* v_auxDeclNGen_1938_; lean_object* v_cache_1939_; lean_object* v_recordedDeps_1940_; lean_object* v_messages_1941_; lean_object* v_infoState_1942_; lean_object* v_snapshotTasks_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1973_; 
v___x_1933_ = lean_st_ref_take(v___y_1925_);
v_traceState_1934_ = lean_ctor_get(v___x_1933_, 4);
v_env_1935_ = lean_ctor_get(v___x_1933_, 0);
v_nextMacroScope_1936_ = lean_ctor_get(v___x_1933_, 1);
v_ngen_1937_ = lean_ctor_get(v___x_1933_, 2);
v_auxDeclNGen_1938_ = lean_ctor_get(v___x_1933_, 3);
v_cache_1939_ = lean_ctor_get(v___x_1933_, 5);
v_recordedDeps_1940_ = lean_ctor_get(v___x_1933_, 6);
v_messages_1941_ = lean_ctor_get(v___x_1933_, 7);
v_infoState_1942_ = lean_ctor_get(v___x_1933_, 8);
v_snapshotTasks_1943_ = lean_ctor_get(v___x_1933_, 9);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1945_ = v___x_1933_;
v_isShared_1946_ = v_isSharedCheck_1973_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snapshotTasks_1943_);
lean_inc(v_infoState_1942_);
lean_inc(v_messages_1941_);
lean_inc(v_recordedDeps_1940_);
lean_inc(v_cache_1939_);
lean_inc(v_traceState_1934_);
lean_inc(v_auxDeclNGen_1938_);
lean_inc(v_ngen_1937_);
lean_inc(v_nextMacroScope_1936_);
lean_inc(v_env_1935_);
lean_dec(v___x_1933_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1973_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
uint64_t v_tid_1947_; lean_object* v_traces_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1972_; 
v_tid_1947_ = lean_ctor_get_uint64(v_traceState_1934_, sizeof(void*)*1);
v_traces_1948_ = lean_ctor_get(v_traceState_1934_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_traceState_1934_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1950_ = v_traceState_1934_;
v_isShared_1951_ = v_isSharedCheck_1972_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_traces_1948_);
lean_dec(v_traceState_1934_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1972_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; double v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1955_ = 0;
v___x_1956_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1957_, 0, v_cls_1920_);
lean_ctor_set(v___x_1957_, 1, v___x_1953_);
lean_ctor_set(v___x_1957_, 2, v___x_1956_);
lean_ctor_set_float(v___x_1957_, sizeof(void*)*3, v___x_1954_);
lean_ctor_set_float(v___x_1957_, sizeof(void*)*3 + 8, v___x_1954_);
lean_ctor_set_uint8(v___x_1957_, sizeof(void*)*3 + 16, v___x_1955_);
v___x_1958_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1959_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v_a_1929_);
lean_ctor_set(v___x_1959_, 2, v___x_1958_);
lean_inc(v_ref_1927_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_ref_1927_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = l_Lean_PersistentArray_push___redArg(v_traces_1948_, v___x_1960_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1961_);
v___x_1963_ = v___x_1950_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1961_);
lean_ctor_set_uint64(v_reuseFailAlloc_1971_, sizeof(void*)*1, v_tid_1947_);
v___x_1963_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 4, v___x_1963_);
v___x_1965_ = v___x_1945_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_env_1935_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_nextMacroScope_1936_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_ngen_1937_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_auxDeclNGen_1938_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 5, v_cache_1939_);
lean_ctor_set(v_reuseFailAlloc_1970_, 6, v_recordedDeps_1940_);
lean_ctor_set(v_reuseFailAlloc_1970_, 7, v_messages_1941_);
lean_ctor_set(v_reuseFailAlloc_1970_, 8, v_infoState_1942_);
lean_ctor_set(v_reuseFailAlloc_1970_, 9, v_snapshotTasks_1943_);
v___x_1965_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_st_ref_put(v___y_1925_, v___x_1965_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1952_);
v___x_1968_ = v___x_1931_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1952_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1975_, lean_object* v_msg_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1975_, v_msg_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
if (lean_obj_tag(v_as_1986_) == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
return v___x_1995_;
}
else
{
lean_object* v_toCold_1996_; lean_object* v_options_1997_; uint8_t v_hasTrace_1998_; 
v_toCold_1996_ = lean_ctor_get(v___y_1991_, 0);
v_options_1997_ = lean_ctor_get(v_toCold_1996_, 2);
v_hasTrace_1998_ = lean_ctor_get_uint8(v_options_1997_, sizeof(void*)*1);
if (v_hasTrace_1998_ == 0)
{
lean_object* v_tail_1999_; 
v_tail_1999_ = lean_ctor_get(v_as_1986_, 1);
lean_inc(v_tail_1999_);
lean_dec_ref_known(v_as_1986_, 2);
v_as_1986_ = v_tail_1999_;
goto _start;
}
else
{
lean_object* v_head_2001_; lean_object* v_tail_2002_; lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v_inheritedTraceOptions_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_head_2001_ = lean_ctor_get(v_as_1986_, 0);
lean_inc(v_head_2001_);
v_tail_2002_ = lean_ctor_get(v_as_1986_, 1);
lean_inc(v_tail_2002_);
lean_dec_ref_known(v_as_1986_, 2);
v_fst_2003_ = lean_ctor_get(v_head_2001_, 0);
lean_inc_n(v_fst_2003_, 2);
v_snd_2004_ = lean_ctor_get(v_head_2001_, 1);
lean_inc(v_snd_2004_);
lean_dec(v_head_2001_);
v_inheritedTraceOptions_2005_ = lean_ctor_get(v_toCold_1996_, 11);
v___x_2006_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2007_ = l_Lean_Name_append(v___x_2006_, v_fst_2003_);
v___x_2008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2005_, v_options_1997_, v___x_2007_);
lean_dec(v___x_2007_);
if (v___x_2008_ == 0)
{
lean_dec(v_snd_2004_);
lean_dec(v_fst_2003_);
v_as_1986_ = v_tail_2002_;
goto _start;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_snd_2004_);
v___x_2011_ = l_Lean_MessageData_ofFormat(v___x_2010_);
v___x_2012_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_2003_, v___x_2011_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref_known(v___x_2012_, 1);
v_as_1986_ = v_tail_2002_;
goto _start;
}
else
{
lean_dec(v_tail_2002_);
return v___x_2012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_currNamespace_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_currNamespace_2023_);
lean_ctor_set(v___x_2026_, 1, v___y_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_currNamespace_2027_, v___y_2028_, v___y_2029_);
lean_dec_ref(v___y_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object* v_opts_2031_, lean_object* v_opt_2032_){
_start:
{
lean_object* v_name_2033_; lean_object* v_defValue_2034_; lean_object* v_map_2035_; lean_object* v___x_2036_; 
v_name_2033_ = lean_ctor_get(v_opt_2032_, 0);
v_defValue_2034_ = lean_ctor_get(v_opt_2032_, 1);
v_map_2035_ = lean_ctor_get(v_opts_2031_, 0);
v___x_2036_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2035_, v_name_2033_);
if (lean_obj_tag(v___x_2036_) == 0)
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_unbox(v_defValue_2034_);
return v___x_2037_;
}
else
{
lean_object* v_val_2038_; 
v_val_2038_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2036_, 1);
if (lean_obj_tag(v_val_2038_) == 1)
{
uint8_t v_v_2039_; 
v_v_2039_ = lean_ctor_get_uint8(v_val_2038_, 0);
lean_dec_ref_known(v_val_2038_, 0);
return v_v_2039_;
}
else
{
uint8_t v___x_2040_; 
lean_dec(v_val_2038_);
v___x_2040_ = lean_unbox(v_defValue_2034_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object* v_opts_2041_, lean_object* v_opt_2042_){
_start:
{
uint8_t v_res_2043_; lean_object* v_r_2044_; 
v_res_2043_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_2041_, v_opt_2042_);
lean_dec_ref(v_opt_2042_);
lean_dec_ref(v_opts_2041_);
v_r_2044_ = lean_box(v_res_2043_);
return v_r_2044_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_box(1);
v___x_2046_ = l_Lean_MessageData_ofFormat(v___x_2045_);
return v___x_2046_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2));
v___x_2051_ = l_Lean_MessageData_ofFormat(v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
if (lean_obj_tag(v_x_2053_) == 0)
{
return v_x_2052_;
}
else
{
lean_object* v_head_2054_; lean_object* v_tail_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2077_; 
v_head_2054_ = lean_ctor_get(v_x_2053_, 0);
v_tail_2055_ = lean_ctor_get(v_x_2053_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2053_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2057_ = v_x_2053_;
v_isShared_2058_ = v_isSharedCheck_2077_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_tail_2055_);
lean_inc(v_head_2054_);
lean_dec(v_x_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2077_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_before_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2075_; 
v_before_2059_ = lean_ctor_get(v_head_2054_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_head_2054_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_head_2054_, 1);
lean_dec(v_unused_2076_);
v___x_2061_ = v_head_2054_;
v_isShared_2062_ = v_isSharedCheck_2075_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_before_2059_);
lean_dec(v_head_2054_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2075_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 7);
lean_ctor_set(v___x_2061_, 1, v___x_2063_);
lean_ctor_set(v___x_2061_, 0, v_x_2052_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_x_2052_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 7);
lean_ctor_set(v___x_2057_, 1, v___x_2066_);
lean_ctor_set(v___x_2057_, 0, v___x_2065_);
v___x_2068_ = v___x_2057_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = l_Lean_MessageData_ofSyntax(v_before_2059_);
v___x_2070_ = l_Lean_indentD(v___x_2069_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2068_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v_x_2052_ = v___x_2071_;
v_x_2053_ = v_tail_2055_;
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
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1));
v___x_2082_ = l_Lean_MessageData_ofFormat(v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object* v_msgData_2083_, lean_object* v_macroStack_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2085_);
v___x_2088_ = l_Lean_Elab_pp_macroStack;
v___x_2089_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v___x_2087_, v___x_2088_);
lean_dec_ref(v___x_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v_macroStack_2084_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_msgData_2083_);
return v___x_2090_;
}
else
{
if (lean_obj_tag(v_macroStack_2084_) == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_msgData_2083_);
return v___x_2091_;
}
else
{
lean_object* v_head_2092_; lean_object* v_after_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2108_; 
v_head_2092_ = lean_ctor_get(v_macroStack_2084_, 0);
lean_inc(v_head_2092_);
v_after_2093_ = lean_ctor_get(v_head_2092_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_head_2092_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v_head_2092_, 0);
lean_dec(v_unused_2109_);
v___x_2095_ = v_head_2092_;
v_isShared_2096_ = v_isSharedCheck_2108_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_after_2093_);
lean_dec(v_head_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2108_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 7);
lean_ctor_set(v___x_2095_, 1, v___x_2097_);
lean_ctor_set(v___x_2095_, 0, v_msgData_2083_);
v___x_2099_ = v___x_2095_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_msgData_2083_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_msgData_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2100_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = l_Lean_MessageData_ofSyntax(v_after_2093_);
v___x_2103_ = l_Lean_indentD(v___x_2102_);
v_msgData_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2104_, 0, v___x_2101_);
lean_ctor_set(v_msgData_2104_, 1, v___x_2103_);
v___x_2105_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_2104_, v_macroStack_2084_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object* v_msgData_2110_, lean_object* v_macroStack_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2110_, v_macroStack_2111_, v___y_2112_);
lean_dec_ref(v___y_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_ref_2123_; lean_object* v_macroStack_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2137_; 
v_ref_2123_ = lean_ctor_get(v___y_2120_, 2);
v_macroStack_2124_ = lean_ctor_get(v___y_2116_, 1);
v___x_2125_ = l_Lean_Elab_getBetterRef(v_ref_2123_, v_macroStack_2124_);
v___x_2126_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_2115_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
lean_inc(v_macroStack_2124_);
v___x_2128_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_2127_, v_macroStack_2124_, v___y_2120_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2125_);
lean_ctor_set(v___x_2133_, 1, v_a_2129_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 1);
lean_ctor_set(v___x_2131_, 0, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_toCold_2156_; lean_object* v_currRecDepth_2157_; lean_object* v_ref_2158_; uint16_t v_optionFlags_2159_; uint8_t v_suppressElabErrors_2160_; uint8_t v_isRecordingDeps_2161_; lean_object* v_ref_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_toCold_2156_ = lean_ctor_get(v___y_2153_, 0);
v_currRecDepth_2157_ = lean_ctor_get(v___y_2153_, 1);
v_ref_2158_ = lean_ctor_get(v___y_2153_, 2);
v_optionFlags_2159_ = lean_ctor_get_uint16(v___y_2153_, sizeof(void*)*3);
v_suppressElabErrors_2160_ = lean_ctor_get_uint8(v___y_2153_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2161_ = lean_ctor_get_uint8(v___y_2153_, sizeof(void*)*3 + 3);
v_ref_2162_ = l_Lean_replaceRef(v_ref_2147_, v_ref_2158_);
lean_inc(v_currRecDepth_2157_);
lean_inc_ref(v_toCold_2156_);
v___x_2163_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2163_, 0, v_toCold_2156_);
lean_ctor_set(v___x_2163_, 1, v_currRecDepth_2157_);
lean_ctor_set(v___x_2163_, 2, v_ref_2162_);
lean_ctor_set_uint16(v___x_2163_, sizeof(void*)*3, v_optionFlags_2159_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*3 + 2, v_suppressElabErrors_2160_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*3 + 3, v_isRecordingDeps_2161_);
v___x_2164_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___x_2163_, v___y_2154_);
lean_dec_ref_known(v___x_2163_, 3);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2165_, lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2165_, v_msg_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v_ref_2165_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2175_, lean_object* v_currNamespace_2176_, lean_object* v_openDecls_2177_, lean_object* v_n_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = l_Lean_ResolveName_resolveNamespace(v_env_2175_, v_currNamespace_2176_, v_openDecls_2177_, v_n_2178_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2183_, lean_object* v_currNamespace_2184_, lean_object* v_openDecls_2185_, lean_object* v_n_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2183_, v_currNamespace_2184_, v_openDecls_2185_, v_n_2186_, v___y_2187_, v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object* v_keys_2190_, lean_object* v_i_2191_, lean_object* v_k_2192_){
_start:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_array_get_size(v_keys_2190_);
v___x_2194_ = lean_nat_dec_lt(v_i_2191_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_dec(v_i_2191_);
return v___x_2194_;
}
else
{
lean_object* v_k_x27_2195_; uint8_t v___x_2196_; 
v_k_x27_2195_ = lean_array_fget_borrowed(v_keys_2190_, v_i_2191_);
v___x_2196_ = l_Lean_instBEqExtraModUse_beq(v_k_2192_, v_k_x27_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = lean_nat_add(v_i_2191_, v___x_2197_);
lean_dec(v_i_2191_);
v_i_2191_ = v___x_2198_;
goto _start;
}
else
{
lean_dec(v_i_2191_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object* v_keys_2200_, lean_object* v_i_2201_, lean_object* v_k_2202_){
_start:
{
uint8_t v_res_2203_; lean_object* v_r_2204_; 
v_res_2203_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2200_, v_i_2201_, v_k_2202_);
lean_dec_ref(v_k_2202_);
lean_dec_ref(v_keys_2200_);
v_r_2204_ = lean_box(v_res_2203_);
return v_r_2204_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object* v_x_2205_, size_t v_x_2206_, lean_object* v_x_2207_){
_start:
{
if (lean_obj_tag(v_x_2205_) == 0)
{
lean_object* v_es_2208_; lean_object* v___x_2209_; size_t v___x_2210_; size_t v___x_2211_; lean_object* v_j_2212_; lean_object* v___x_2213_; 
v_es_2208_ = lean_ctor_get(v_x_2205_, 0);
v___x_2209_ = lean_box(2);
v___x_2210_ = ((size_t)31ULL);
v___x_2211_ = lean_usize_land(v_x_2206_, v___x_2210_);
v_j_2212_ = lean_usize_to_nat(v___x_2211_);
v___x_2213_ = lean_array_get_borrowed(v___x_2209_, v_es_2208_, v_j_2212_);
lean_dec(v_j_2212_);
switch(lean_obj_tag(v___x_2213_))
{
case 0:
{
lean_object* v_key_2214_; uint8_t v___x_2215_; 
v_key_2214_ = lean_ctor_get(v___x_2213_, 0);
v___x_2215_ = l_Lean_instBEqExtraModUse_beq(v_x_2207_, v_key_2214_);
return v___x_2215_;
}
case 1:
{
lean_object* v_node_2216_; size_t v___x_2217_; size_t v___x_2218_; 
v_node_2216_ = lean_ctor_get(v___x_2213_, 0);
v___x_2217_ = ((size_t)5ULL);
v___x_2218_ = lean_usize_shift_right(v_x_2206_, v___x_2217_);
v_x_2205_ = v_node_2216_;
v_x_2206_ = v___x_2218_;
goto _start;
}
default: 
{
uint8_t v___x_2220_; 
v___x_2220_ = 0;
return v___x_2220_;
}
}
}
else
{
lean_object* v_ks_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_ks_2221_ = lean_ctor_get(v_x_2205_, 0);
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_2221_, v___x_2222_, v_x_2207_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
size_t v_x_29672__boxed_2227_; uint8_t v_res_2228_; lean_object* v_r_2229_; 
v_x_29672__boxed_2227_ = lean_unbox_usize(v_x_2225_);
lean_dec(v_x_2225_);
v_res_2228_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2224_, v_x_29672__boxed_2227_, v_x_2226_);
lean_dec_ref(v_x_2226_);
lean_dec_ref(v_x_2224_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
uint64_t v___x_2232_; size_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2232_ = l_Lean_instHashableExtraModUse_hash(v_x_2231_);
v___x_2233_ = lean_uint64_to_usize(v___x_2232_);
v___x_2234_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2230_, v___x_2233_, v_x_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object* v_x_2235_, lean_object* v_x_2236_){
_start:
{
uint8_t v_res_2237_; lean_object* v_r_2238_; 
v_res_2237_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2235_, v_x_2236_);
lean_dec_ref(v_x_2236_);
lean_dec_ref(v_x_2235_);
v_r_2238_ = lean_box(v_res_2237_);
return v_r_2238_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v_cls_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_cls_2251_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2252_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2253_ = l_Lean_Name_append(v___x_2252_, v_cls_2251_);
return v___x_2253_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2264_, uint8_t v_isMeta_2265_, lean_object* v_hint_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_env_2276_; uint8_t v_isExporting_2277_; lean_object* v_entry_2278_; lean_object* v___x_2279_; lean_object* v_env_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2274_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0);
v___x_2275_ = lean_st_ref_get(v___y_2272_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_env_2276_);
lean_dec(v___x_2275_);
v_isExporting_2277_ = lean_ctor_get_uint8(v_env_2276_, sizeof(void*)*8);
lean_dec_ref(v_env_2276_);
lean_inc(v_mod_2264_);
v_entry_2278_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2278_, 0, v_mod_2264_);
lean_ctor_set_uint8(v_entry_2278_, sizeof(void*)*1, v_isExporting_2277_);
lean_ctor_set_uint8(v_entry_2278_, sizeof(void*)*1 + 1, v_isMeta_2265_);
v___x_2279_ = lean_st_ref_get(v___y_2272_);
v_env_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc_ref(v_env_2280_);
lean_dec(v___x_2279_);
v___x_2281_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2282_ = lean_box(1);
v___x_2283_ = lean_box(0);
v___x_2327_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2274_, v___x_2281_, v_env_2280_, v___x_2282_, v___x_2283_);
v___x_2328_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_2327_, v_entry_2278_);
lean_dec(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v_toCold_2329_; lean_object* v_options_2330_; uint8_t v_hasTrace_2331_; 
v_toCold_2329_ = lean_ctor_get(v___y_2271_, 0);
v_options_2330_ = lean_ctor_get(v_toCold_2329_, 2);
v_hasTrace_2331_ = lean_ctor_get_uint8(v_options_2330_, sizeof(void*)*1);
if (v_hasTrace_2331_ == 0)
{
lean_dec(v_hint_2266_);
lean_dec(v_mod_2264_);
v___y_2285_ = v___y_2270_;
v___y_2286_ = v___y_2272_;
goto v___jp_2284_;
}
else
{
lean_object* v_inheritedTraceOptions_2332_; lean_object* v_cls_2333_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_inheritedTraceOptions_2332_ = lean_ctor_get(v_toCold_2329_, 11);
v_cls_2333_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2353_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2354_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2332_, v_options_2330_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_dec(v_hint_2266_);
lean_dec(v_mod_2264_);
v___y_2285_ = v___y_2270_;
v___y_2286_ = v___y_2272_;
goto v___jp_2284_;
}
else
{
lean_object* v___x_2355_; lean_object* v___y_2357_; 
v___x_2355_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
if (v_isExporting_2277_ == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2357_ = v___x_2364_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2365_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2357_ = v___x_2365_;
goto v___jp_2356_;
}
v___jp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_inc_ref(v___y_2357_);
v___x_2358_ = l_Lean_stringToMessageData(v___y_2357_);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2355_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
if (v_isMeta_2265_ == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___y_2340_ = v___x_2361_;
v___y_2341_ = v___x_2362_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2363_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14));
v___y_2340_ = v___x_2361_;
v___y_2341_ = v___x_2363_;
goto v___jp_2339_;
}
}
}
v___jp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___y_2335_);
lean_ctor_set(v___x_2337_, 1, v___y_2336_);
v___x_2338_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2333_, v___x_2337_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_dec_ref_known(v___x_2338_, 1);
v___y_2285_ = v___y_2270_;
v___y_2286_ = v___y_2272_;
goto v___jp_2284_;
}
else
{
lean_dec_ref_known(v_entry_2278_, 1);
return v___x_2338_;
}
}
v___jp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
lean_inc_ref(v___y_2341_);
v___x_2342_ = l_Lean_stringToMessageData(v___y_2341_);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___y_2340_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_MessageData_ofName(v_mod_2264_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = l_Lean_Name_isAnonymous(v_hint_2266_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2350_ = l_Lean_MessageData_ofName(v_hint_2266_);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___y_2335_ = v___x_2347_;
v___y_2336_ = v___x_2351_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2352_; 
lean_dec(v_hint_2266_);
v___x_2352_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7);
v___y_2335_ = v___x_2347_;
v___y_2336_ = v___x_2352_;
goto v___jp_2334_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec_ref_known(v_entry_2278_, 1);
lean_dec(v_hint_2266_);
lean_dec(v_mod_2264_);
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
v___jp_2284_:
{
lean_object* v___x_2287_; lean_object* v_toEnvExtension_2288_; lean_object* v_env_2289_; lean_object* v_nextMacroScope_2290_; lean_object* v_ngen_2291_; lean_object* v_auxDeclNGen_2292_; lean_object* v_traceState_2293_; lean_object* v_recordedDeps_2294_; lean_object* v_messages_2295_; lean_object* v_infoState_2296_; lean_object* v_snapshotTasks_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2325_; 
v___x_2287_ = lean_st_ref_take(v___y_2286_);
v_toEnvExtension_2288_ = lean_ctor_get(v___x_2281_, 0);
v_env_2289_ = lean_ctor_get(v___x_2287_, 0);
v_nextMacroScope_2290_ = lean_ctor_get(v___x_2287_, 1);
v_ngen_2291_ = lean_ctor_get(v___x_2287_, 2);
v_auxDeclNGen_2292_ = lean_ctor_get(v___x_2287_, 3);
v_traceState_2293_ = lean_ctor_get(v___x_2287_, 4);
v_recordedDeps_2294_ = lean_ctor_get(v___x_2287_, 6);
v_messages_2295_ = lean_ctor_get(v___x_2287_, 7);
v_infoState_2296_ = lean_ctor_get(v___x_2287_, 8);
v_snapshotTasks_2297_ = lean_ctor_get(v___x_2287_, 9);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2287_, 5);
lean_dec(v_unused_2326_);
v___x_2299_ = v___x_2287_;
v_isShared_2300_ = v_isSharedCheck_2325_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_snapshotTasks_2297_);
lean_inc(v_infoState_2296_);
lean_inc(v_messages_2295_);
lean_inc(v_recordedDeps_2294_);
lean_inc(v_traceState_2293_);
lean_inc(v_auxDeclNGen_2292_);
lean_inc(v_ngen_2291_);
lean_inc(v_nextMacroScope_2290_);
lean_inc(v_env_2289_);
lean_dec(v___x_2287_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2325_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_asyncMode_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v_asyncMode_2301_ = lean_ctor_get(v_toEnvExtension_2288_, 2);
v___x_2302_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2281_, v_env_2289_, v_entry_2278_, v_asyncMode_2301_, v___x_2283_);
v___x_2303_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 5, v___x_2303_);
lean_ctor_set(v___x_2299_, 0, v___x_2302_);
v___x_2305_ = v___x_2299_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_nextMacroScope_2290_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v_ngen_2291_);
lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_auxDeclNGen_2292_);
lean_ctor_set(v_reuseFailAlloc_2324_, 4, v_traceState_2293_);
lean_ctor_set(v_reuseFailAlloc_2324_, 5, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2324_, 6, v_recordedDeps_2294_);
lean_ctor_set(v_reuseFailAlloc_2324_, 7, v_messages_2295_);
lean_ctor_set(v_reuseFailAlloc_2324_, 8, v_infoState_2296_);
lean_ctor_set(v_reuseFailAlloc_2324_, 9, v_snapshotTasks_2297_);
v___x_2305_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_mctx_2308_; lean_object* v_zetaDeltaFVarIds_2309_; lean_object* v_postponed_2310_; lean_object* v_diag_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2322_; 
v___x_2306_ = lean_st_ref_put(v___y_2286_, v___x_2305_);
v___x_2307_ = lean_st_ref_take(v___y_2285_);
v_mctx_2308_ = lean_ctor_get(v___x_2307_, 0);
v_zetaDeltaFVarIds_2309_ = lean_ctor_get(v___x_2307_, 2);
v_postponed_2310_ = lean_ctor_get(v___x_2307_, 3);
v_diag_2311_ = lean_ctor_get(v___x_2307_, 4);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2307_, 1);
lean_dec(v_unused_2323_);
v___x_2313_ = v___x_2307_;
v_isShared_2314_ = v_isSharedCheck_2322_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_diag_2311_);
lean_inc(v_postponed_2310_);
lean_inc(v_zetaDeltaFVarIds_2309_);
lean_inc(v_mctx_2308_);
lean_dec(v___x_2307_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2322_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2316_);
v___x_2318_ = v___x_2313_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_mctx_2308_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_zetaDeltaFVarIds_2309_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_postponed_2310_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_diag_2311_);
v___x_2318_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_st_ref_put(v___y_2285_, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2315_);
return v___x_2320_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2368_, lean_object* v_isMeta_2369_, lean_object* v_hint_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
uint8_t v_isMeta_boxed_2378_; lean_object* v_res_2379_; 
v_isMeta_boxed_2378_ = lean_unbox(v_isMeta_2369_);
v_res_2379_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2368_, v_isMeta_boxed_2378_, v_hint_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2380_, lean_object* v_declName_2381_, lean_object* v_as_2382_, size_t v_sz_2383_, size_t v_i_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v_declName_2381_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_b_2385_);
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v_modules_2396_; lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v_toImport_2400_; lean_object* v_module_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; 
v___x_2395_ = l_Lean_Environment_header(v___x_2380_);
v_modules_2396_ = lean_ctor_get(v___x_2395_, 3);
lean_inc_ref(v_modules_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2398_ = lean_array_uget_borrowed(v_as_2382_, v_i_2384_);
v___x_2399_ = lean_array_get(v___x_2397_, v_modules_2396_, v_a_2398_);
lean_dec_ref(v_modules_2396_);
v_toImport_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc_ref(v_toImport_2400_);
lean_dec(v___x_2399_);
v_module_2401_ = lean_ctor_get(v_toImport_2400_, 0);
lean_inc(v_module_2401_);
lean_dec_ref(v_toImport_2400_);
v___x_2402_ = lean_box(0);
v___x_2403_ = 0;
lean_inc(v_declName_2381_);
v___x_2404_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2401_, v___x_2403_, v_declName_2381_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2404_) == 0)
{
size_t v___x_2405_; size_t v___x_2406_; 
lean_dec_ref_known(v___x_2404_, 1);
v___x_2405_ = ((size_t)1ULL);
v___x_2406_ = lean_usize_add(v_i_2384_, v___x_2405_);
v_i_2384_ = v___x_2406_;
v_b_2385_ = v___x_2402_;
goto _start;
}
else
{
lean_dec(v_declName_2381_);
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2408_, lean_object* v_declName_2409_, lean_object* v_as_2410_, lean_object* v_sz_2411_, lean_object* v_i_2412_, lean_object* v_b_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
size_t v_sz_boxed_2421_; size_t v_i_boxed_2422_; lean_object* v_res_2423_; 
v_sz_boxed_2421_ = lean_unbox_usize(v_sz_2411_);
lean_dec(v_sz_2411_);
v_i_boxed_2422_ = lean_unbox_usize(v_i_2412_);
lean_dec(v_i_2412_);
v_res_2423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2408_, v_declName_2409_, v_as_2410_, v_sz_boxed_2421_, v_i_boxed_2422_, v_b_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec_ref(v_as_2410_);
lean_dec_ref(v___x_2408_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object* v_a_2424_, lean_object* v_x_2425_){
_start:
{
if (lean_obj_tag(v_x_2425_) == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
else
{
lean_object* v_key_2427_; lean_object* v_value_2428_; lean_object* v_tail_2429_; uint8_t v___x_2430_; 
v_key_2427_ = lean_ctor_get(v_x_2425_, 0);
v_value_2428_ = lean_ctor_get(v_x_2425_, 1);
v_tail_2429_ = lean_ctor_get(v_x_2425_, 2);
v___x_2430_ = lean_name_eq(v_key_2427_, v_a_2424_);
if (v___x_2430_ == 0)
{
v_x_2425_ = v_tail_2429_;
goto _start;
}
else
{
lean_object* v___x_2432_; 
lean_inc(v_value_2428_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_value_2428_);
return v___x_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object* v_a_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2433_, v_x_2434_);
lean_dec(v_x_2434_);
lean_dec(v_a_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_buckets_2438_; lean_object* v___x_2439_; uint64_t v___y_2441_; 
v_buckets_2438_ = lean_ctor_get(v_m_2436_, 1);
v___x_2439_ = lean_array_get_size(v_buckets_2438_);
if (lean_obj_tag(v_a_2437_) == 0)
{
uint64_t v___x_2455_; 
v___x_2455_ = 1723ULL;
v___y_2441_ = v___x_2455_;
goto v___jp_2440_;
}
else
{
uint64_t v_hash_2456_; 
v_hash_2456_ = lean_ctor_get_uint64(v_a_2437_, sizeof(void*)*2);
v___y_2441_ = v_hash_2456_;
goto v___jp_2440_;
}
v___jp_2440_:
{
uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v_fold_2444_; uint64_t v___x_2445_; uint64_t v___x_2446_; uint64_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2442_ = 32ULL;
v___x_2443_ = lean_uint64_shift_right(v___y_2441_, v___x_2442_);
v_fold_2444_ = lean_uint64_xor(v___y_2441_, v___x_2443_);
v___x_2445_ = 16ULL;
v___x_2446_ = lean_uint64_shift_right(v_fold_2444_, v___x_2445_);
v___x_2447_ = lean_uint64_xor(v_fold_2444_, v___x_2446_);
v___x_2448_ = lean_uint64_to_usize(v___x_2447_);
v___x_2449_ = lean_usize_of_nat(v___x_2439_);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_sub(v___x_2449_, v___x_2450_);
v___x_2452_ = lean_usize_land(v___x_2448_, v___x_2451_);
v___x_2453_ = lean_array_uget_borrowed(v_buckets_2438_, v___x_2452_);
v___x_2454_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2437_, v___x_2453_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2457_, v_a_2458_);
lean_dec(v_a_2458_);
lean_dec_ref(v_m_2457_);
return v_res_2459_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2463_, uint8_t v_isMeta_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_env_2477_; lean_object* v___y_2479_; lean_object* v___x_2492_; 
v___x_2472_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0);
v___x_2473_ = lean_st_ref_get(v___y_2470_);
v_env_2477_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_env_2477_);
lean_dec(v___x_2473_);
v___x_2492_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2477_, v_declName_2463_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_dec_ref(v_env_2477_);
lean_dec(v_declName_2463_);
goto v___jp_2474_;
}
else
{
lean_object* v_val_2493_; lean_object* v___x_2494_; lean_object* v_modules_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_val_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = l_Lean_Environment_header(v_env_2477_);
v_modules_2495_ = lean_ctor_get(v___x_2494_, 3);
lean_inc_ref(v_modules_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = lean_array_get_size(v_modules_2495_);
v___x_2497_ = lean_nat_dec_lt(v_val_2493_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_dec_ref(v_modules_2495_);
lean_dec(v_val_2493_);
lean_dec_ref(v_env_2477_);
lean_dec(v_declName_2463_);
goto v___jp_2474_;
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___y_2501_; 
v___x_2498_ = lean_array_fget(v_modules_2495_, v_val_2493_);
lean_dec(v_val_2493_);
lean_dec_ref(v_modules_2495_);
v___x_2499_ = lean_st_ref_get(v___y_2470_);
if (v_isMeta_2464_ == 0)
{
lean_dec(v___x_2499_);
v___y_2501_ = v_isMeta_2464_;
goto v___jp_2500_;
}
else
{
lean_object* v_env_2512_; uint8_t v___x_2513_; 
v_env_2512_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_ref(v_env_2512_);
lean_dec(v___x_2499_);
lean_inc(v_declName_2463_);
v___x_2513_ = l_Lean_isMarkedMeta(v_env_2512_, v_declName_2463_);
if (v___x_2513_ == 0)
{
v___y_2501_ = v_isMeta_2464_;
goto v___jp_2500_;
}
else
{
uint8_t v___x_2514_; 
v___x_2514_ = 0;
v___y_2501_ = v___x_2514_;
goto v___jp_2500_;
}
}
v___jp_2500_:
{
lean_object* v_toImport_2502_; lean_object* v_module_2503_; lean_object* v___x_2504_; 
v_toImport_2502_ = lean_ctor_get(v___x_2498_, 0);
lean_inc_ref(v_toImport_2502_);
lean_dec(v___x_2498_);
v_module_2503_ = lean_ctor_get(v_toImport_2502_, 0);
lean_inc(v_module_2503_);
lean_dec_ref(v_toImport_2502_);
lean_inc(v_declName_2463_);
v___x_2504_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2503_, v___y_2501_, v_declName_2463_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref_known(v___x_2504_, 1);
v___x_2505_ = l_Lean_indirectModUseExt;
v___x_2506_ = lean_box(1);
v___x_2507_ = lean_box(0);
lean_inc_ref(v_env_2477_);
v___x_2508_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2472_, v___x_2505_, v_env_2477_, v___x_2506_, v___x_2507_);
v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2508_, v_declName_2463_);
lean_dec(v___x_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___y_2479_ = v___x_2510_;
goto v___jp_2478_;
}
else
{
lean_object* v_val_2511_; 
v_val_2511_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_val_2511_);
lean_dec_ref_known(v___x_2509_, 1);
v___y_2479_ = v_val_2511_;
goto v___jp_2478_;
}
}
else
{
lean_dec_ref(v_env_2477_);
lean_dec(v_declName_2463_);
return v___x_2504_;
}
}
}
}
v___jp_2474_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
v___jp_2478_:
{
lean_object* v___x_2480_; size_t v_sz_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2480_ = lean_box(0);
v_sz_2481_ = lean_array_size(v___y_2479_);
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2477_, v_declName_2463_, v___y_2479_, v_sz_2481_, v___x_2482_, v___x_2480_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_env_2477_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2483_, 0);
lean_dec(v_unused_2491_);
v___x_2485_ = v___x_2483_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_dec(v___x_2483_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2480_);
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2480_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2515_, lean_object* v_isMeta_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v_isMeta_boxed_2524_; lean_object* v_res_2525_; 
v_isMeta_boxed_2524_ = lean_unbox(v_isMeta_2516_);
v_res_2525_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2515_, v_isMeta_boxed_2524_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
if (lean_obj_tag(v_as_x27_2526_) == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_b_2527_);
return v___x_2535_;
}
else
{
lean_object* v_head_2536_; lean_object* v_tail_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; 
v_head_2536_ = lean_ctor_get(v_as_x27_2526_, 0);
v_tail_2537_ = lean_ctor_get(v_as_x27_2526_, 1);
v___x_2538_ = lean_box(0);
v___x_2539_ = 1;
lean_inc(v_head_2536_);
v___x_2540_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2536_, v___x_2539_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
v_as_x27_2526_ = v_tail_2537_;
v_b_2527_ = v___x_2538_;
goto _start;
}
else
{
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2542_, lean_object* v_b_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2542_, v_b_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v_as_x27_2542_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_env_2552_, lean_object* v___x_2553_, lean_object* v_currNamespace_2554_, lean_object* v_openDecls_2555_, lean_object* v_n_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = l_Lean_ResolveName_resolveGlobalName(v_env_2552_, v___x_2553_, v_currNamespace_2554_, v_openDecls_2555_, v_n_2556_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___y_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_env_2561_, lean_object* v___x_2562_, lean_object* v_currNamespace_2563_, lean_object* v_openDecls_2564_, lean_object* v_n_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_env_2561_, v___x_2562_, v_currNamespace_2563_, v_openDecls_2564_, v_n_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec_ref(v___x_2562_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2569_, lean_object* v_declName_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
uint8_t v___x_2573_; lean_object* v_env_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; uint8_t v___x_2577_; 
v___x_2573_ = 0;
v_env_2574_ = l_Lean_Environment_setExporting(v_env_2569_, v___x_2573_);
lean_inc(v_declName_2570_);
v___x_2575_ = l_Lean_mkPrivateName(v_env_2574_, v_declName_2570_);
v___x_2576_ = 1;
lean_inc_ref(v_env_2574_);
v___x_2577_ = l_Lean_Environment_contains(v_env_2574_, v___x_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2578_ = l_Lean_privateToUserName(v_declName_2570_);
v___x_2579_ = l_Lean_Environment_contains(v_env_2574_, v___x_2578_, v___x_2576_);
v___x_2580_ = lean_box(v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___y_2572_);
return v___x_2581_;
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec_ref(v_env_2574_);
lean_dec(v_declName_2570_);
v___x_2582_ = lean_box(v___x_2577_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___y_2572_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2584_, lean_object* v_declName_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2584_, v_declName_2585_, v___y_2586_, v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2588_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = l_Lean_maxRecDepthErrorMessage;
v___x_2595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2597_ = l_Lean_MessageData_ofFormat(v___x_2596_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2599_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2600_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2601_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_ref_2601_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; lean_object* v_toCold_2619_; lean_object* v_env_2620_; lean_object* v_currRecDepth_2621_; lean_object* v_ref_2622_; lean_object* v_maxRecDepth_2623_; lean_object* v_currNamespace_2624_; lean_object* v_openDecls_2625_; lean_object* v_quotContext_2626_; lean_object* v_currMacroScope_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v_methods_2634_; lean_object* v___x_2635_; lean_object* v_nextMacroScope_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2618_ = lean_st_ref_get(v___y_2616_);
v_toCold_2619_ = lean_ctor_get(v___y_2615_, 0);
v_env_2620_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_ref_n(v_env_2620_, 4);
lean_dec(v___x_2618_);
v_currRecDepth_2621_ = lean_ctor_get(v___y_2615_, 1);
v_ref_2622_ = lean_ctor_get(v___y_2615_, 2);
v_maxRecDepth_2623_ = lean_ctor_get(v_toCold_2619_, 3);
v_currNamespace_2624_ = lean_ctor_get(v_toCold_2619_, 4);
v_openDecls_2625_ = lean_ctor_get(v_toCold_2619_, 5);
v_quotContext_2626_ = lean_ctor_get(v_toCold_2619_, 8);
v_currMacroScope_2627_ = lean_ctor_get(v_toCold_2619_, 9);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2628_, 0, v_env_2620_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2629_, 0, v_env_2620_);
v___x_2630_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2615_);
lean_inc_n(v_currNamespace_2624_, 3);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2631_, 0, v_currNamespace_2624_);
lean_inc_n(v_openDecls_2625_, 2);
v___f_2632_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2632_, 0, v_env_2620_);
lean_closure_set(v___f_2632_, 1, v___x_2630_);
lean_closure_set(v___f_2632_, 2, v_currNamespace_2624_);
lean_closure_set(v___f_2632_, 3, v_openDecls_2625_);
v___f_2633_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2633_, 0, v_env_2620_);
lean_closure_set(v___f_2633_, 1, v_currNamespace_2624_);
lean_closure_set(v___f_2633_, 2, v_openDecls_2625_);
v_methods_2634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2634_, 0, v___f_2629_);
lean_ctor_set(v_methods_2634_, 1, v___f_2631_);
lean_ctor_set(v_methods_2634_, 2, v___f_2628_);
lean_ctor_set(v_methods_2634_, 3, v___f_2633_);
lean_ctor_set(v_methods_2634_, 4, v___f_2632_);
v___x_2635_ = lean_st_ref_get(v___y_2616_);
v_nextMacroScope_2636_ = lean_ctor_get(v___x_2635_, 1);
lean_inc(v_nextMacroScope_2636_);
lean_dec(v___x_2635_);
lean_inc(v_ref_2622_);
lean_inc(v_maxRecDepth_2623_);
lean_inc(v_currRecDepth_2621_);
lean_inc(v_currMacroScope_2627_);
lean_inc(v_quotContext_2626_);
v___x_2637_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2637_, 0, v_methods_2634_);
lean_ctor_set(v___x_2637_, 1, v_quotContext_2626_);
lean_ctor_set(v___x_2637_, 2, v_currMacroScope_2627_);
lean_ctor_set(v___x_2637_, 3, v_currRecDepth_2621_);
lean_ctor_set(v___x_2637_, 4, v_maxRecDepth_2623_);
lean_ctor_set(v___x_2637_, 5, v_ref_2622_);
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2639_, 0, v_nextMacroScope_2636_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
lean_ctor_set(v___x_2639_, 2, v___x_2638_);
v___x_2640_ = lean_apply_2(v_x_2610_, v___x_2637_, v___x_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v_a_2642_; lean_object* v_macroScope_2643_; lean_object* v_traceMsgs_2644_; lean_object* v_expandedMacroDecls_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_a_2641_);
v_a_2642_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2640_, 2);
v_macroScope_2643_ = lean_ctor_get(v_a_2641_, 0);
lean_inc(v_macroScope_2643_);
v_traceMsgs_2644_ = lean_ctor_get(v_a_2641_, 1);
lean_inc(v_traceMsgs_2644_);
v_expandedMacroDecls_2645_ = lean_ctor_get(v_a_2641_, 2);
lean_inc(v_expandedMacroDecls_2645_);
lean_dec(v_a_2641_);
v___x_2646_ = lean_box(0);
v___x_2647_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2645_, v___x_2646_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v_expandedMacroDecls_2645_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; lean_object* v_env_2649_; lean_object* v_ngen_2650_; lean_object* v_auxDeclNGen_2651_; lean_object* v_traceState_2652_; lean_object* v_cache_2653_; lean_object* v_recordedDeps_2654_; lean_object* v_messages_2655_; lean_object* v_infoState_2656_; lean_object* v_snapshotTasks_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref_known(v___x_2647_, 1);
v___x_2648_ = lean_st_ref_take(v___y_2616_);
v_env_2649_ = lean_ctor_get(v___x_2648_, 0);
v_ngen_2650_ = lean_ctor_get(v___x_2648_, 2);
v_auxDeclNGen_2651_ = lean_ctor_get(v___x_2648_, 3);
v_traceState_2652_ = lean_ctor_get(v___x_2648_, 4);
v_cache_2653_ = lean_ctor_get(v___x_2648_, 5);
v_recordedDeps_2654_ = lean_ctor_get(v___x_2648_, 6);
v_messages_2655_ = lean_ctor_get(v___x_2648_, 7);
v_infoState_2656_ = lean_ctor_get(v___x_2648_, 8);
v_snapshotTasks_2657_ = lean_ctor_get(v___x_2648_, 9);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2648_, 1);
lean_dec(v_unused_2684_);
v___x_2659_ = v___x_2648_;
v_isShared_2660_ = v_isSharedCheck_2683_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snapshotTasks_2657_);
lean_inc(v_infoState_2656_);
lean_inc(v_messages_2655_);
lean_inc(v_recordedDeps_2654_);
lean_inc(v_cache_2653_);
lean_inc(v_traceState_2652_);
lean_inc(v_auxDeclNGen_2651_);
lean_inc(v_ngen_2650_);
lean_inc(v_env_2649_);
lean_dec(v___x_2648_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2683_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v_macroScope_2643_);
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_env_2649_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_macroScope_2643_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_ngen_2650_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_auxDeclNGen_2651_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_traceState_2652_);
lean_ctor_set(v_reuseFailAlloc_2682_, 5, v_cache_2653_);
lean_ctor_set(v_reuseFailAlloc_2682_, 6, v_recordedDeps_2654_);
lean_ctor_set(v_reuseFailAlloc_2682_, 7, v_messages_2655_);
lean_ctor_set(v_reuseFailAlloc_2682_, 8, v_infoState_2656_);
lean_ctor_set(v_reuseFailAlloc_2682_, 9, v_snapshotTasks_2657_);
v___x_2662_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_st_ref_put(v___y_2616_, v___x_2662_);
v___x_2664_ = l_List_reverse___redArg(v_traceMsgs_2644_);
v___x_2665_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2664_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2665_, 0);
lean_dec(v_unused_2673_);
v___x_2667_ = v___x_2665_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v___x_2665_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v_a_2642_);
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2642_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v_a_2642_);
v_a_2674_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2665_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2665_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_traceMsgs_2644_);
lean_dec(v_macroScope_2643_);
lean_dec(v_a_2642_);
v_a_2685_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2647_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2647_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v_a_2693_; 
v_a_2693_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2640_, 2);
if (lean_obj_tag(v_a_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_a_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_a_2694_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_a_2694_);
v_a_2695_ = lean_ctor_get(v_a_2693_, 1);
lean_inc_ref(v_a_2695_);
lean_dec_ref_known(v_a_2693_, 2);
v___x_2696_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2697_ = lean_string_dec_eq(v_a_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_a_2695_);
v___x_2699_ = l_Lean_MessageData_ofFormat(v___x_2698_);
v___x_2700_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2694_, v___x_2699_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v_a_2694_);
return v___x_2700_;
}
else
{
lean_object* v___x_2701_; 
lean_dec_ref(v_a_2695_);
v___x_2701_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2694_);
return v___x_2701_;
}
}
else
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v_res_2711_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2714_ = l_Lean_mkConst(v___x_2713_, v___x_2712_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_box(0);
v___x_2727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2728_ = l_Lean_mkConst(v___x_2727_, v___x_2726_);
return v___x_2728_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2731_, lean_object* v_as_2732_, size_t v_sz_2733_, size_t v_i_2734_, lean_object* v_b_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_a_2744_; uint8_t v___x_2748_; 
v___x_2748_ = lean_usize_dec_lt(v_i_2734_, v_sz_2733_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_b_2735_);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v_a_2752_; uint8_t v___x_2753_; 
v___x_2750_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2751_ = lean_box(0);
v_a_2752_ = lean_array_uget_borrowed(v_as_2732_, v_i_2734_);
lean_inc(v_a_2752_);
v___x_2753_ = l_Lean_Syntax_isOfKind(v_a_2752_, v___x_2750_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_dec_ref_known(v___x_2754_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2754_;
}
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2755_ = lean_unsigned_to_nat(0u);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = l_Lean_Syntax_getArg(v_a_2752_, v___x_2755_);
v___x_2758_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2757_);
v___x_2759_ = l_Lean_Syntax_isOfKind(v___x_2757_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2760_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2757_);
v___x_2761_ = l_Lean_Syntax_isOfKind(v___x_2757_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_dec(v___x_2757_);
v___x_2762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_dec_ref_known(v___x_2762_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2762_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___y_2765_; uint8_t v___y_2766_; lean_object* v___y_2767_; uint64_t v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___x_2785_; lean_object* v___y_2787_; 
v___x_2763_ = lean_box(0);
v___x_2785_ = l_Lean_Syntax_getArg(v___x_2757_, v___x_2755_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2785_);
v___x_2859_ = l_Lean_Syntax_isOfKind(v___x_2785_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec(v___x_2785_);
lean_dec(v___x_2757_);
v___x_2860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref_known(v___x_2860_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2860_;
}
}
else
{
goto v___jp_2853_;
}
}
else
{
goto v___jp_2853_;
}
v___jp_2764_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0);
lean_inc_n(v___y_2765_, 2);
v___x_2776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2776_, 0, v___y_2765_);
lean_ctor_set(v___x_2776_, 1, v___x_2763_);
lean_ctor_set(v___x_2776_, 2, v___x_2775_);
v___x_2777_ = lean_box(0);
v___x_2778_ = 1;
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___y_2765_);
lean_ctor_set(v___x_2779_, 1, v___x_2763_);
v___x_2780_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2780_, 0, v___x_2776_);
lean_ctor_set(v___x_2780_, 1, v___y_2767_);
lean_ctor_set(v___x_2780_, 2, v___x_2777_);
lean_ctor_set(v___x_2780_, 3, v___x_2779_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*4, v___x_2778_);
v___x_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
v___x_2782_ = l_Lean_addAndCompile(v___x_2781_, v___x_2731_, v___x_2759_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_dec_ref_known(v___x_2782_, 1);
if (v___y_2766_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v___y_2768_, v___y_2765_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_dec_ref_known(v___x_2783_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2783_;
}
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v___y_2768_, v___y_2765_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref_known(v___x_2784_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2784_;
}
}
}
else
{
lean_dec(v___y_2765_);
return v___x_2782_;
}
}
v___jp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2788_, 0, v___x_2785_);
v___x_2789_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2788_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = l_Lean_Widget_elabWidgetInstanceSpec(v___y_2787_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc_n(v_a_2792_, 2);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2792_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2793_) == 0)
{
uint8_t v___x_2794_; 
v___x_2794_ = lean_unbox(v_a_2790_);
if (v___x_2794_ == 1)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; 
lean_dec(v_a_2792_);
lean_dec(v_a_2790_);
v_a_2795_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2796_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2795_, v___y_2739_, v___y_2741_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_dec_ref_known(v___x_2796_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2796_;
}
}
else
{
lean_object* v_a_2797_; lean_object* v_id_2798_; uint64_t v_javascriptHash_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2797_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2793_, 1);
v_id_2798_ = lean_ctor_get(v_a_2797_, 0);
lean_inc(v_id_2798_);
v_javascriptHash_2799_ = lean_ctor_get_uint64(v_a_2797_, sizeof(void*)*2);
lean_dec(v_a_2797_);
v___x_2800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2));
v___x_2801_ = l_Lean_Name_append(v_id_2798_, v___x_2800_);
v___x_2802_ = l_Lean_Core_mkFreshUserName(v___x_2801_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2792_, v___y_2739_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; uint8_t v___x_2806_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = l_Lean_Expr_hasMVar(v_a_2805_);
if (v___x_2806_ == 0)
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
v___y_2765_ = v_a_2803_;
v___y_2766_ = v___x_2807_;
v___y_2767_ = v_a_2805_;
v___y_2768_ = v_javascriptHash_2799_;
v___y_2769_ = v___y_2736_;
v___y_2770_ = v___y_2737_;
v___y_2771_ = v___y_2738_;
v___y_2772_ = v___y_2739_;
v___y_2773_ = v___y_2740_;
v___y_2774_ = v___y_2741_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2805_);
v___x_2809_ = l_Lean_indentExpr(v_a_2805_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2810_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2811_) == 0)
{
uint8_t v___x_2812_; 
lean_dec_ref_known(v___x_2811_, 1);
v___x_2812_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
v___y_2765_ = v_a_2803_;
v___y_2766_ = v___x_2812_;
v___y_2767_ = v_a_2805_;
v___y_2768_ = v_javascriptHash_2799_;
v___y_2769_ = v___y_2736_;
v___y_2770_ = v___y_2737_;
v___y_2771_ = v___y_2738_;
v___y_2772_ = v___y_2739_;
v___y_2773_ = v___y_2740_;
v___y_2774_ = v___y_2741_;
goto v___jp_2764_;
}
else
{
lean_dec(v_a_2805_);
lean_dec(v_a_2803_);
lean_dec(v_a_2790_);
return v___x_2811_;
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_a_2803_);
lean_dec(v_a_2790_);
v_a_2813_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2804_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2804_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec(v_a_2792_);
lean_dec(v_a_2790_);
v_a_2821_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2802_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2802_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2792_);
lean_dec(v_a_2790_);
v_a_2829_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2793_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2793_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_a_2790_);
v_a_2837_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2791_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2791_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v___y_2787_);
v_a_2845_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2789_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2789_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
v___jp_2853_:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_Syntax_getArg(v___x_2757_, v___x_2756_);
lean_dec(v___x_2757_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2854_);
v___x_2856_ = l_Lean_Syntax_isOfKind(v___x_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec(v___x_2854_);
lean_dec(v___x_2785_);
v___x_2857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref_known(v___x_2857_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2857_;
}
}
else
{
v___y_2787_ = v___x_2854_;
goto v___jp_2786_;
}
}
else
{
v___y_2787_ = v___x_2854_;
goto v___jp_2786_;
}
}
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = l_Lean_Syntax_getArg(v___x_2757_, v___x_2756_);
lean_dec(v___x_2757_);
v___x_2862_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2861_);
v___x_2863_ = l_Lean_Syntax_isOfKind(v___x_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec(v___x_2861_);
v___x_2864_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref_known(v___x_2864_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2864_;
}
}
else
{
lean_object* v_toCold_2865_; lean_object* v_ref_2866_; lean_object* v_quotContext_2867_; lean_object* v_currMacroScope_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_toCold_2865_ = lean_ctor_get(v___y_2740_, 0);
v_ref_2866_ = lean_ctor_get(v___y_2740_, 2);
v_quotContext_2867_ = lean_ctor_get(v_toCold_2865_, 8);
v_currMacroScope_2868_ = lean_ctor_get(v_toCold_2865_, 9);
v___x_2869_ = 0;
v___x_2870_ = l_Lean_SourceInfo_fromRef(v_ref_2866_, v___x_2869_);
v___x_2871_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2872_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2873_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2868_);
lean_inc(v_quotContext_2867_);
v___x_2874_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2873_, v_currMacroScope_2868_);
v___x_2875_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2870_, 2);
v___x_2876_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2870_);
lean_ctor_set(v___x_2876_, 1, v___x_2872_);
lean_ctor_set(v___x_2876_, 2, v___x_2874_);
lean_ctor_set(v___x_2876_, 3, v___x_2875_);
v___x_2877_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2878_ = l_Lean_Syntax_node1(v___x_2870_, v___x_2877_, v___x_2861_);
v___x_2879_ = l_Lean_Syntax_node2(v___x_2870_, v___x_2871_, v___x_2876_, v___x_2878_);
v___x_2880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2881_ = l_Lean_Elab_Term_elabTerm(v___x_2879_, v___x_2880_, v___x_2731_, v___x_2731_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2882_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; uint64_t v_javascriptHash_2885_; lean_object* v___x_2886_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v_javascriptHash_2885_ = lean_ctor_get_uint64(v_a_2884_, sizeof(void*)*1);
lean_dec(v_a_2884_);
v___x_2886_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2885_, v___y_2739_, v___y_2741_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_dec_ref_known(v___x_2886_, 1);
v_a_2744_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
return v___x_2886_;
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
v_a_2887_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2883_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2883_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
v_a_2895_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2881_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2881_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
}
v___jp_2743_:
{
size_t v___x_2745_; size_t v___x_2746_; 
v___x_2745_ = ((size_t)1ULL);
v___x_2746_ = lean_usize_add(v_i_2734_, v___x_2745_);
v_i_2734_ = v___x_2746_;
v_b_2735_ = v_a_2744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2903_, lean_object* v_as_2904_, lean_object* v_sz_2905_, lean_object* v_i_2906_, lean_object* v_b_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_30566__boxed_2915_; size_t v_sz_boxed_2916_; size_t v_i_boxed_2917_; lean_object* v_res_2918_; 
v___x_30566__boxed_2915_ = lean_unbox(v___x_2903_);
v_sz_boxed_2916_ = lean_unbox_usize(v_sz_2905_);
lean_dec(v_sz_2905_);
v_i_boxed_2917_ = lean_unbox_usize(v_i_2906_);
lean_dec(v_i_2906_);
v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_30566__boxed_2915_, v_as_2904_, v_sz_boxed_2916_, v_i_boxed_2917_, v_b_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec_ref(v_as_2904_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2919_, lean_object* v___x_2920_, size_t v_sz_2921_, size_t v___x_2922_, lean_object* v___x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2919_, v___x_2920_, v_sz_2921_, v___x_2922_, v___x_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v___x_2931_, 0);
lean_dec(v_unused_2939_);
v___x_2933_ = v___x_2931_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_dec(v___x_2931_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2923_);
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2923_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
else
{
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_2940_, lean_object* v___x_2941_, lean_object* v_sz_2942_, lean_object* v___x_2943_, lean_object* v___x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_30934__boxed_2952_; size_t v_sz_boxed_2953_; size_t v___x_30936__boxed_2954_; lean_object* v_res_2955_; 
v___x_30934__boxed_2952_ = lean_unbox(v___x_2940_);
v_sz_boxed_2953_ = lean_unbox_usize(v_sz_2942_);
lean_dec(v_sz_2942_);
v___x_30936__boxed_2954_ = lean_unbox_usize(v___x_2943_);
lean_dec(v___x_2943_);
v_res_2955_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_30934__boxed_2952_, v___x_2941_, v_sz_boxed_2953_, v___x_30936__boxed_2954_, v___x_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v___x_2941_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_2958_);
v___x_2963_ = l_Lean_Syntax_isOfKind(v_x_2958_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; 
lean_dec(v_x_2958_);
v___x_2964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_2964_;
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v_ws_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; size_t v_sz_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; 
v___x_2965_ = lean_unsigned_to_nat(2u);
v___x_2966_ = l_Lean_Syntax_getArg(v_x_2958_, v___x_2965_);
lean_dec(v_x_2958_);
v_ws_2967_ = l_Lean_Syntax_getArgs(v___x_2966_);
lean_dec(v___x_2966_);
v___x_2968_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_2967_);
lean_dec_ref(v_ws_2967_);
v___x_2969_ = lean_box(0);
v_sz_2970_ = lean_array_size(v___x_2968_);
v___x_2971_ = lean_box(v___x_2963_);
v___x_2972_ = lean_box_usize(v_sz_2970_);
v___x_2973_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2974_, 0, v___x_2971_);
lean_closure_set(v___f_2974_, 1, v___x_2968_);
lean_closure_set(v___f_2974_, 2, v___x_2972_);
lean_closure_set(v___f_2974_, 3, v___x_2973_);
lean_closure_set(v___f_2974_, 4, v___x_2969_);
v___x_2975_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2974_, v_a_2959_, v_a_2960_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_2976_, v_a_2977_, v_a_2978_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_2981_, lean_object* v_x_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2982_, v___y_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_2986_, v_x_2987_, v___y_2988_, v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_x_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_2991_, lean_object* v_ref_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2992_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3001_, lean_object* v_ref_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3001_, v_ref_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3011_, lean_object* v_x_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3021_, v_x_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3031_, v___y_3035_, v___y_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object* v_00_u03b1_3049_, lean_object* v_00_u03b2_3050_, lean_object* v_00_u03c3_3051_, lean_object* v_ext_3052_, lean_object* v_b_3053_, uint8_t v_kind_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_3052_, v_b_3053_, v_kind_3054_, v___y_3058_, v___y_3059_, v___y_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object* v_00_u03b1_3063_, lean_object* v_00_u03b2_3064_, lean_object* v_00_u03c3_3065_, lean_object* v_ext_3066_, lean_object* v_b_3067_, lean_object* v_kind_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v_kind_boxed_3076_; lean_object* v_res_3077_; 
v_kind_boxed_3076_ = lean_unbox(v_kind_3068_);
v_res_3077_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_3063_, v_00_u03b2_3064_, v_00_u03c3_3065_, v_ext_3066_, v_b_3067_, v_kind_boxed_3076_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3078_, lean_object* v_msg_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3088_, lean_object* v_msg_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3088_, v_msg_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3098_, v___y_3102_, v___y_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
uint64_t v_h_boxed_3115_; lean_object* v_res_3116_; 
v_h_boxed_3115_ = lean_unbox_uint64(v_h_3107_);
lean_dec_ref(v_h_3107_);
v_res_3116_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3115_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3117_, lean_object* v_msg_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3117_, v_msg_3118_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3127_, lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3127_, v_msg_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3137_, lean_object* v_as_x27_3138_, lean_object* v_b_3139_, lean_object* v_a_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3138_, v_b_3139_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3149_, lean_object* v_as_x27_3150_, lean_object* v_b_3151_, lean_object* v_a_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3149_, v_as_x27_3150_, v_b_3151_, v_a_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v_as_x27_3150_);
lean_dec(v_as_3149_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3161_, lean_object* v_ref_3162_, lean_object* v_msg_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3162_, v_msg_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3172_, lean_object* v_ref_3173_, lean_object* v_msg_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3172_, v_ref_3173_, v_msg_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v_ref_3173_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3183_, lean_object* v_t_3184_, uint64_t v_k_3185_, lean_object* v_fallback_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3184_, v_k_3185_, v_fallback_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3188_, lean_object* v_t_3189_, lean_object* v_k_3190_, lean_object* v_fallback_3191_){
_start:
{
uint64_t v_k_boxed_3192_; lean_object* v_res_3193_; 
v_k_boxed_3192_ = lean_unbox_uint64(v_k_3190_);
lean_dec_ref(v_k_3190_);
v_res_3193_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3188_, v_t_3189_, v_k_boxed_3192_, v_fallback_3191_);
lean_dec(v_fallback_3191_);
lean_dec(v_t_3189_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3194_, uint64_t v_k_3195_, lean_object* v_v_3196_, lean_object* v_t_3197_, lean_object* v_hl_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3195_, v_v_3196_, v_t_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3200_, lean_object* v_k_3201_, lean_object* v_v_3202_, lean_object* v_t_3203_, lean_object* v_hl_3204_){
_start:
{
uint64_t v_k_boxed_3205_; lean_object* v_res_3206_; 
v_k_boxed_3205_ = lean_unbox_uint64(v_k_3201_);
lean_dec_ref(v_k_3201_);
v_res_3206_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3200_, v_k_boxed_3205_, v_v_3202_, v_t_3203_, v_hl_3204_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_3207_, lean_object* v_macroStack_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_3207_, v_macroStack_3208_, v___y_3213_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_3217_, lean_object* v_macroStack_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3217_, v_macroStack_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object* v_00_u03b2_3227_, uint64_t v_k_3228_, lean_object* v_t_3229_, lean_object* v_h_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3228_, v_t_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object* v_00_u03b2_3232_, lean_object* v_k_3233_, lean_object* v_t_3234_, lean_object* v_h_3235_){
_start:
{
uint64_t v_k_boxed_3236_; lean_object* v_res_3237_; 
v_k_boxed_3236_ = lean_unbox_uint64(v_k_3233_);
lean_dec_ref(v_k_3233_);
v_res_3237_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_3232_, v_k_boxed_3236_, v_t_3234_, v_h_3235_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3238_, lean_object* v_m_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3239_, v_a_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3242_, lean_object* v_m_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3242_, v_m_3243_, v_a_3244_);
lean_dec(v_a_3244_);
lean_dec_ref(v_m_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object* v_00_u03b2_3246_, lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_3247_, v_x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object* v_00_u03b2_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_3250_, v_x_3251_, v_x_3252_);
lean_dec_ref(v_x_3252_);
lean_dec_ref(v_x_3251_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object* v_00_u03b2_3255_, lean_object* v_a_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_3256_, v_x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_3259_, v_a_3260_, v_x_3261_);
lean_dec(v_x_3261_);
lean_dec(v_a_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object* v_00_u03b2_3263_, lean_object* v_x_3264_, size_t v_x_3265_, lean_object* v_x_3266_){
_start:
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_3264_, v_x_3265_, v_x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
size_t v_x_31298__boxed_3272_; uint8_t v_res_3273_; lean_object* v_r_3274_; 
v_x_31298__boxed_3272_ = lean_unbox_usize(v_x_3270_);
lean_dec(v_x_3270_);
v_res_3273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_3268_, v_x_3269_, v_x_31298__boxed_3272_, v_x_3271_);
lean_dec_ref(v_x_3271_);
lean_dec_ref(v_x_3269_);
v_r_3274_ = lean_box(v_res_3273_);
return v_r_3274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object* v_00_u03b2_3275_, lean_object* v_keys_3276_, lean_object* v_vals_3277_, lean_object* v_heq_3278_, lean_object* v_i_3279_, lean_object* v_k_3280_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_3276_, v_i_3279_, v_k_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_keys_3283_, lean_object* v_vals_3284_, lean_object* v_heq_3285_, lean_object* v_i_3286_, lean_object* v_k_3287_){
_start:
{
uint8_t v_res_3288_; lean_object* v_r_3289_; 
v_res_3288_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_3282_, v_keys_3283_, v_vals_3284_, v_heq_3285_, v_i_3286_, v_k_3287_);
lean_dec_ref(v_k_3287_);
lean_dec_ref(v_vals_3284_);
lean_dec_ref(v_keys_3283_);
v_r_3289_ = lean_box(v_res_3288_);
return v_r_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3307_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3317_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; uint64_t v_javascriptHash_3320_; lean_object* v_props_3321_; lean_object* v___x_3322_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v_javascriptHash_3320_ = lean_ctor_get_uint64(v_a_3319_, sizeof(void*)*2);
v_props_3321_ = lean_ctor_get(v_a_3319_, 1);
lean_inc_ref(v_props_3321_);
lean_dec(v_a_3319_);
v___x_3322_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3320_, v_props_3321_, v_x_3308_, v___y_3313_, v___y_3314_);
return v___x_3322_;
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_x_3308_);
v_a_3323_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3318_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3318_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec(v_x_3308_);
v_a_3331_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3316_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3316_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3339_, lean_object* v_x_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3339_, v_x_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3349_);
v___x_3354_ = l_Lean_Syntax_isOfKind(v_x_3349_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v_x_3349_);
v___x_3355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; lean_object* v_s_3357_; lean_object* v___f_3358_; lean_object* v___x_3359_; 
v___x_3356_ = lean_unsigned_to_nat(1u);
v_s_3357_ = l_Lean_Syntax_getArg(v_x_3349_, v___x_3356_);
v___f_3358_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3358_, 0, v_s_3357_);
lean_closure_set(v___f_3358_, 1, v_x_3349_);
v___x_3359_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3358_, v_a_3350_, v_a_3351_);
return v___x_3359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Widget_elabWidgetCmd(v_x_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3364_;
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
