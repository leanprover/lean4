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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(lean_object* v_mod_226_, lean_object* v_props_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
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
LEAN_EXPORT void l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_226_ = stack[0].m_obj;
lean_object* v_props_227_ = stack[1].m_obj;
lean_object* v_a_228_ = stack[2].m_obj;
lean_object* v_a_229_ = stack[3].m_obj;
lean_object* v_a_230_ = stack[4].m_obj;
lean_object* v_a_231_ = stack[5].m_obj;
lean_object* v_a_232_ = stack[6].m_obj;
lean_object* v_a_233_ = stack[7].m_obj;
lean_object* v_res_340_;
v_res_340_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_226_, v_props_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___boxed(lean_object* v_mod_341_, lean_object* v_props_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_341_, v_props_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_350_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_box(0);
v___x_352_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
return v___x_353_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg(){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_357_;
v_res_357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___boxed(lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v_res_359_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(lean_object* v_00_u03b1_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_368_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_361_ = stack[1].m_obj;
lean_object* v___y_362_ = stack[2].m_obj;
lean_object* v___y_363_ = stack[3].m_obj;
lean_object* v___y_364_ = stack[4].m_obj;
lean_object* v___y_365_ = stack[5].m_obj;
lean_object* v___y_366_ = stack[6].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(lean_box(0), v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(v_00_u03b1_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__0));
v___x_381_ = l_String_toRawSubstring_x27(v___x_380_);
return v___x_381_;
}
}
lean_object* l_Lean_Widget_elabWidgetInstanceSpec(lean_object* v_x_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v_x_402_);
v___x_411_ = l_Lean_Syntax_isOfKind(v_x_402_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v_x_402_);
v___x_412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v_mod_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v_mod_414_ = l_Lean_Syntax_getArg(v_x_402_, v___x_413_);
v___x_415_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v_mod_414_);
v___x_416_ = l_Lean_Syntax_isOfKind(v_mod_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec(v_mod_414_);
lean_dec(v_x_402_);
v___x_417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = l_Lean_Syntax_getArg(v_x_402_, v___x_418_);
lean_dec(v_x_402_);
lean_inc(v___x_419_);
v___x_420_ = l_Lean_Syntax_matchesNull(v___x_419_, v___x_413_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_419_);
v___x_422_ = l_Lean_Syntax_matchesNull(v___x_419_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v___x_419_);
lean_dec(v_mod_414_);
v___x_423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_423_;
}
else
{
lean_object* v_props_424_; lean_object* v___x_425_; 
v_props_424_ = l_Lean_Syntax_getArg(v___x_419_, v___x_418_);
lean_dec(v___x_419_);
v___x_425_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_414_, v_props_424_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_425_;
}
}
else
{
lean_object* v_toCold_426_; lean_object* v_ref_427_; lean_object* v_quotContext_428_; lean_object* v_currMacroScope_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v___x_419_);
v_toCold_426_ = lean_ctor_get(v_a_407_, 0);
v_ref_427_ = lean_ctor_get(v_a_407_, 2);
v_quotContext_428_ = lean_ctor_get(v_toCold_426_, 8);
v_currMacroScope_429_ = lean_ctor_get(v_toCold_426_, 9);
v___x_430_ = 0;
v___x_431_ = l_Lean_SourceInfo_fromRef(v_ref_427_, v___x_430_);
v___x_432_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_433_ = lean_obj_once(&l_Lean_Widget_elabWidgetInstanceSpec___closed__1, &l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once, _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1);
v___x_434_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__4));
lean_inc(v_currMacroScope_429_);
lean_inc(v_quotContext_428_);
v___x_435_ = l_Lean_addMacroScope(v_quotContext_428_, v___x_434_, v_currMacroScope_429_);
v___x_436_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__7));
lean_inc_n(v___x_431_, 6);
v___x_437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_437_, 0, v___x_431_);
lean_ctor_set(v___x_437_, 1, v___x_433_);
lean_ctor_set(v___x_437_, 2, v___x_435_);
lean_ctor_set(v___x_437_, 3, v___x_436_);
v___x_438_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_439_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__9));
v___x_440_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__10));
v___x_441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_431_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_431_);
lean_ctor_set(v___x_443_, 1, v___x_438_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
v___x_444_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__11));
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_431_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_Syntax_node3(v___x_431_, v___x_439_, v___x_441_, v___x_443_, v___x_445_);
v___x_447_ = l_Lean_Syntax_node1(v___x_431_, v___x_438_, v___x_446_);
v___x_448_ = l_Lean_Syntax_node2(v___x_431_, v___x_432_, v___x_437_, v___x_447_);
v___x_449_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_414_, v___x_448_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_elabWidgetInstanceSpec_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_402_ = stack[0].m_obj;
lean_object* v_a_403_ = stack[1].m_obj;
lean_object* v_a_404_ = stack[2].m_obj;
lean_object* v_a_405_ = stack[3].m_obj;
lean_object* v_a_406_ = stack[4].m_obj;
lean_object* v_a_407_ = stack[5].m_obj;
lean_object* v_a_408_ = stack[6].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_Widget_elabWidgetInstanceSpec(v_x_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec___boxed(lean_object* v_x_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Widget_elabWidgetInstanceSpec(v_x_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
return v_res_459_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_556_;
v_res_556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg___boxed(lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v_res_558_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(lean_object* v_00_u03b1_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_563_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_560_ = stack[1].m_obj;
lean_object* v___y_561_ = stack[2].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(lean_box(0), v___y_560_, v___y_561_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___boxed(lean_object* v_00_u03b1_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(v_00_u03b1_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_569_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(lean_object* v_e_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_Expr_hasMVar(v_e_570_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v_e_570_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v_mctx_576_; lean_object* v___x_577_; lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v___x_580_; lean_object* v_cache_581_; lean_object* v_zetaDeltaFVarIds_582_; lean_object* v_postponed_583_; lean_object* v_diag_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_593_; 
v___x_575_ = lean_st_ref_get(v___y_571_);
v_mctx_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_mctx_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_instantiateMVarsCore(v_mctx_576_, v_e_570_);
v_fst_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_fst_578_);
v_snd_579_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_snd_579_);
lean_dec_ref(v___x_577_);
v___x_580_ = lean_st_ref_take(v___y_571_);
v_cache_581_ = lean_ctor_get(v___x_580_, 1);
v_zetaDeltaFVarIds_582_ = lean_ctor_get(v___x_580_, 2);
v_postponed_583_ = lean_ctor_get(v___x_580_, 3);
v_diag_584_ = lean_ctor_get(v___x_580_, 4);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_594_);
v___x_586_ = v___x_580_;
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_diag_584_);
lean_inc(v_postponed_583_);
lean_inc(v_zetaDeltaFVarIds_582_);
lean_inc(v_cache_581_);
lean_dec(v___x_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_snd_579_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_snd_579_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_cache_581_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_zetaDeltaFVarIds_582_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_postponed_583_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v_diag_584_);
v___x_589_ = v_reuseFailAlloc_592_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_st_ref_put(v___y_571_, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v_fst_578_);
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_570_ = stack[0].m_obj;
lean_object* v___y_571_ = stack[1].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_570_, v___y_571_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(lean_object* v_e_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_596_, v___y_597_);
lean_dec(v___y_597_);
return v_res_599_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(lean_object* v_e_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_600_, v___y_604_);
return v___x_608_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_600_ = stack[0].m_obj;
lean_object* v___y_601_ = stack[1].m_obj;
lean_object* v___y_602_ = stack[2].m_obj;
lean_object* v___y_603_ = stack[3].m_obj;
lean_object* v___y_604_ = stack[4].m_obj;
lean_object* v___y_605_ = stack[5].m_obj;
lean_object* v___y_606_ = stack[6].m_obj;
lean_object* v_res_609_;
v_res_609_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(v_e_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(lean_object* v_e_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(v_e_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_618_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(uint64_t v_k_619_, lean_object* v_t_620_){
_start:
{
if (lean_obj_tag(v_t_620_) == 0)
{
lean_object* v_k_621_; lean_object* v_v_622_; lean_object* v_l_623_; lean_object* v_r_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_1281_; 
v_k_621_ = lean_ctor_get(v_t_620_, 1);
v_v_622_ = lean_ctor_get(v_t_620_, 2);
v_l_623_ = lean_ctor_get(v_t_620_, 3);
v_r_624_ = lean_ctor_get(v_t_620_, 4);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_t_620_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_t_620_, 0);
lean_dec(v_unused_1282_);
v___x_626_ = v_t_620_;
v_isShared_627_ = v_isSharedCheck_1281_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_r_624_);
lean_inc(v_l_623_);
lean_inc(v_v_622_);
lean_inc(v_k_621_);
lean_dec(v_t_620_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_1281_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint64_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_unbox_uint64(v_k_621_);
v___x_629_ = lean_uint64_dec_lt(v_k_619_, v___x_628_);
if (v___x_629_ == 0)
{
uint64_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unbox_uint64(v_k_621_);
v___x_631_ = lean_uint64_dec_eq(v_k_619_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v_impl_632_; lean_object* v___x_633_; 
v_impl_632_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_619_, v_r_624_);
v___x_633_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_632_) == 0)
{
if (lean_obj_tag(v_l_623_) == 0)
{
lean_object* v_size_634_; lean_object* v_size_635_; lean_object* v_k_636_; lean_object* v_v_637_; lean_object* v_l_638_; lean_object* v_r_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_size_634_ = lean_ctor_get(v_impl_632_, 0);
v_size_635_ = lean_ctor_get(v_l_623_, 0);
v_k_636_ = lean_ctor_get(v_l_623_, 1);
v_v_637_ = lean_ctor_get(v_l_623_, 2);
v_l_638_ = lean_ctor_get(v_l_623_, 3);
v_r_639_ = lean_ctor_get(v_l_623_, 4);
lean_inc(v_r_639_);
v___x_640_ = lean_unsigned_to_nat(3u);
v___x_641_ = lean_nat_mul(v___x_640_, v_size_634_);
v___x_642_ = lean_nat_dec_lt(v___x_641_, v_size_635_);
lean_dec(v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
lean_dec(v_r_639_);
v___x_643_ = lean_nat_add(v___x_633_, v_size_635_);
v___x_644_ = lean_nat_add(v___x_643_, v_size_634_);
lean_dec(v___x_643_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_impl_632_);
lean_ctor_set(v___x_626_, 0, v___x_644_);
v___x_646_ = v___x_626_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_l_623_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_impl_632_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_l_638_);
lean_inc(v_v_637_);
lean_inc(v_k_636_);
lean_inc(v_size_635_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_714_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_l_623_, 2);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_l_623_, 1);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_718_);
v___x_649_ = v_l_623_;
v_isShared_650_ = v_isSharedCheck_713_;
goto v_resetjp_648_;
}
else
{
lean_dec(v_l_623_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_713_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_size_651_; lean_object* v_size_652_; lean_object* v_k_653_; lean_object* v_v_654_; lean_object* v_l_655_; lean_object* v_r_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_size_651_ = lean_ctor_get(v_l_638_, 0);
v_size_652_ = lean_ctor_get(v_r_639_, 0);
v_k_653_ = lean_ctor_get(v_r_639_, 1);
v_v_654_ = lean_ctor_get(v_r_639_, 2);
v_l_655_ = lean_ctor_get(v_r_639_, 3);
v_r_656_ = lean_ctor_get(v_r_639_, 4);
v___x_657_ = lean_unsigned_to_nat(2u);
v___x_658_ = lean_nat_mul(v___x_657_, v_size_651_);
v___x_659_ = lean_nat_dec_lt(v_size_652_, v___x_658_);
lean_dec(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_r_656_);
lean_inc(v_l_655_);
lean_inc(v_v_654_);
lean_inc(v_k_653_);
v_isSharedCheck_688_ = !lean_is_exclusive(v_r_639_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; lean_object* v_unused_693_; 
v_unused_689_ = lean_ctor_get(v_r_639_, 4);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_r_639_, 3);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_r_639_, 2);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_r_639_, 1);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_r_639_, 0);
lean_dec(v_unused_693_);
v___x_661_ = v_r_639_;
v_isShared_662_ = v_isSharedCheck_688_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_r_639_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_688_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___x_676_; lean_object* v___y_678_; 
v___x_663_ = lean_nat_add(v___x_633_, v_size_635_);
lean_dec(v_size_635_);
v___x_664_ = lean_nat_add(v___x_663_, v_size_634_);
lean_dec(v___x_663_);
v___x_676_ = lean_nat_add(v___x_633_, v_size_651_);
if (lean_obj_tag(v_l_655_) == 0)
{
lean_object* v_size_686_; 
v_size_686_ = lean_ctor_get(v_l_655_, 0);
lean_inc(v_size_686_);
v___y_678_ = v_size_686_;
goto v___jp_677_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___y_678_ = v___x_687_;
goto v___jp_677_;
}
v___jp_665_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_nat_add(v___y_666_, v___y_668_);
lean_dec(v___y_668_);
lean_dec(v___y_666_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 4, v_impl_632_);
lean_ctor_set(v___x_661_, 3, v_r_656_);
lean_ctor_set(v___x_661_, 2, v_v_622_);
lean_ctor_set(v___x_661_, 1, v_k_621_);
lean_ctor_set(v___x_661_, 0, v___x_669_);
v___x_671_ = v___x_661_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_r_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_impl_632_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 4, v___x_671_);
lean_ctor_set(v___x_649_, 3, v___y_667_);
lean_ctor_set(v___x_649_, 2, v_v_654_);
lean_ctor_set(v___x_649_, 1, v_k_653_);
lean_ctor_set(v___x_649_, 0, v___x_664_);
v___x_673_ = v___x_649_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_653_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_654_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v___y_667_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_nat_add(v___x_676_, v___y_678_);
lean_dec(v___y_678_);
lean_dec(v___x_676_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_l_655_);
lean_ctor_set(v___x_626_, 3, v_l_638_);
lean_ctor_set(v___x_626_, 2, v_v_637_);
lean_ctor_set(v___x_626_, 1, v_k_636_);
lean_ctor_set(v___x_626_, 0, v___x_679_);
v___x_681_ = v___x_626_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_k_636_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_v_637_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_l_638_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_l_655_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_nat_add(v___x_633_, v_size_634_);
if (lean_obj_tag(v_r_656_) == 0)
{
lean_object* v_size_683_; 
v_size_683_ = lean_ctor_get(v_r_656_, 0);
lean_inc(v_size_683_);
v___y_666_ = v___x_682_;
v___y_667_ = v___x_681_;
v___y_668_ = v_size_683_;
goto v___jp_665_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_unsigned_to_nat(0u);
v___y_666_ = v___x_682_;
v___y_667_ = v___x_681_;
v___y_668_ = v___x_684_;
goto v___jp_665_;
}
}
}
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_del_object(v___x_626_);
v___x_694_ = lean_nat_add(v___x_633_, v_size_635_);
lean_dec(v_size_635_);
v___x_695_ = lean_nat_add(v___x_694_, v_size_634_);
lean_dec(v___x_694_);
v___x_696_ = lean_nat_add(v___x_633_, v_size_634_);
v___x_697_ = lean_nat_add(v___x_696_, v_size_652_);
lean_dec(v___x_696_);
lean_inc_ref(v_impl_632_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 4, v_impl_632_);
lean_ctor_set(v___x_649_, 3, v_r_639_);
lean_ctor_set(v___x_649_, 2, v_v_622_);
lean_ctor_set(v___x_649_, 1, v_k_621_);
lean_ctor_set(v___x_649_, 0, v___x_697_);
v___x_699_ = v___x_649_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_r_639_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_impl_632_);
v___x_699_ = v_reuseFailAlloc_712_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_isSharedCheck_706_ = !lean_is_exclusive(v_impl_632_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_707_ = lean_ctor_get(v_impl_632_, 4);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_impl_632_, 3);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_impl_632_, 2);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_impl_632_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_impl_632_, 0);
lean_dec(v_unused_711_);
v___x_701_ = v_impl_632_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_impl_632_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v___x_699_);
lean_ctor_set(v___x_701_, 3, v_l_638_);
lean_ctor_set(v___x_701_, 2, v_v_637_);
lean_ctor_set(v___x_701_, 1, v_k_636_);
lean_ctor_set(v___x_701_, 0, v___x_695_);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_k_636_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_v_637_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_l_638_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v___x_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v_size_719_ = lean_ctor_get(v_impl_632_, 0);
v___x_720_ = lean_nat_add(v___x_633_, v_size_719_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_impl_632_);
lean_ctor_set(v___x_626_, 0, v___x_720_);
v___x_722_ = v___x_626_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_l_623_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_impl_632_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
if (lean_obj_tag(v_l_623_) == 0)
{
lean_object* v_l_724_; 
v_l_724_ = lean_ctor_get(v_l_623_, 3);
if (lean_obj_tag(v_l_724_) == 0)
{
lean_object* v_r_725_; 
lean_inc_ref(v_l_724_);
v_r_725_ = lean_ctor_get(v_l_623_, 4);
lean_inc(v_r_725_);
if (lean_obj_tag(v_r_725_) == 0)
{
lean_object* v_size_726_; lean_object* v_k_727_; lean_object* v_v_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_741_; 
v_size_726_ = lean_ctor_get(v_l_623_, 0);
v_k_727_ = lean_ctor_get(v_l_623_, 1);
v_v_728_ = lean_ctor_get(v_l_623_, 2);
v_isSharedCheck_741_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; lean_object* v_unused_743_; 
v_unused_742_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_743_);
v___x_730_ = v_l_623_;
v_isShared_731_ = v_isSharedCheck_741_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_v_728_);
lean_inc(v_k_727_);
lean_inc(v_size_726_);
lean_dec(v_l_623_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_741_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_size_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_size_732_ = lean_ctor_get(v_r_725_, 0);
v___x_733_ = lean_nat_add(v___x_633_, v_size_726_);
lean_dec(v_size_726_);
v___x_734_ = lean_nat_add(v___x_633_, v_size_732_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v_impl_632_);
lean_ctor_set(v___x_730_, 3, v_r_725_);
lean_ctor_set(v___x_730_, 2, v_v_622_);
lean_ctor_set(v___x_730_, 1, v_k_621_);
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_r_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_impl_632_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v___x_736_);
lean_ctor_set(v___x_626_, 3, v_l_724_);
lean_ctor_set(v___x_626_, 2, v_v_728_);
lean_ctor_set(v___x_626_, 1, v_k_727_);
lean_ctor_set(v___x_626_, 0, v___x_733_);
v___x_738_ = v___x_626_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_l_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_756_; 
v_k_744_ = lean_ctor_get(v_l_623_, 1);
v_v_745_ = lean_ctor_get(v_l_623_, 2);
v_isSharedCheck_756_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; 
v_unused_757_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_759_);
v___x_747_ = v_l_623_;
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_v_745_);
lean_inc(v_k_744_);
lean_dec(v_l_623_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = lean_unsigned_to_nat(3u);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 3, v_r_725_);
lean_ctor_set(v___x_747_, 2, v_v_622_);
lean_ctor_set(v___x_747_, 1, v_k_621_);
lean_ctor_set(v___x_747_, 0, v___x_633_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_r_725_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_r_725_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v___x_751_);
lean_ctor_set(v___x_626_, 3, v_l_724_);
lean_ctor_set(v___x_626_, 2, v_v_745_);
lean_ctor_set(v___x_626_, 1, v_k_744_);
lean_ctor_set(v___x_626_, 0, v___x_749_);
v___x_753_ = v___x_626_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_744_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_745_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_l_724_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
else
{
lean_object* v_r_760_; 
v_r_760_ = lean_ctor_get(v_l_623_, 4);
lean_inc(v_r_760_);
if (lean_obj_tag(v_r_760_) == 0)
{
lean_object* v_k_761_; lean_object* v_v_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_785_; 
lean_inc(v_l_724_);
v_k_761_ = lean_ctor_get(v_l_623_, 1);
v_v_762_ = lean_ctor_get(v_l_623_, 2);
v_isSharedCheck_785_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; 
v_unused_786_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_788_);
v___x_764_ = v_l_623_;
v_isShared_765_ = v_isSharedCheck_785_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_v_762_);
lean_inc(v_k_761_);
lean_dec(v_l_623_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_785_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_k_766_; lean_object* v_v_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_781_; 
v_k_766_ = lean_ctor_get(v_r_760_, 1);
v_v_767_ = lean_ctor_get(v_r_760_, 2);
v_isSharedCheck_781_ = !lean_is_exclusive(v_r_760_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_782_ = lean_ctor_get(v_r_760_, 4);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_760_, 3);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_r_760_, 0);
lean_dec(v_unused_784_);
v___x_769_ = v_r_760_;
v_isShared_770_ = v_isSharedCheck_781_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_v_767_);
lean_inc(v_k_766_);
lean_dec(v_r_760_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_781_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(3u);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 4, v_l_724_);
lean_ctor_set(v___x_769_, 3, v_l_724_);
lean_ctor_set(v___x_769_, 2, v_v_762_);
lean_ctor_set(v___x_769_, 1, v_k_761_);
lean_ctor_set(v___x_769_, 0, v___x_633_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_k_761_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_v_762_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_l_724_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_l_724_);
v___x_773_ = v_reuseFailAlloc_780_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 4, v_l_724_);
lean_ctor_set(v___x_764_, 2, v_v_622_);
lean_ctor_set(v___x_764_, 1, v_k_621_);
lean_ctor_set(v___x_764_, 0, v___x_633_);
v___x_775_ = v___x_764_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_l_724_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_l_724_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v___x_775_);
lean_ctor_set(v___x_626_, 3, v___x_773_);
lean_ctor_set(v___x_626_, 2, v_v_767_);
lean_ctor_set(v___x_626_, 1, v_k_766_);
lean_ctor_set(v___x_626_, 0, v___x_771_);
v___x_777_ = v___x_626_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_766_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_767_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_unsigned_to_nat(2u);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_r_760_);
lean_ctor_set(v___x_626_, 0, v___x_789_);
v___x_791_ = v___x_626_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v_l_623_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_r_760_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_794_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_l_623_);
lean_ctor_set(v___x_626_, 0, v___x_633_);
v___x_794_ = v___x_626_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_l_623_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_l_623_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_del_object(v___x_626_);
lean_dec(v_v_622_);
lean_dec(v_k_621_);
if (lean_obj_tag(v_l_623_) == 0)
{
if (lean_obj_tag(v_r_624_) == 0)
{
lean_object* v_size_796_; lean_object* v_k_797_; lean_object* v_v_798_; lean_object* v_l_799_; lean_object* v_r_800_; lean_object* v_size_801_; lean_object* v_k_802_; lean_object* v_v_803_; lean_object* v_l_804_; lean_object* v_r_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_size_796_ = lean_ctor_get(v_l_623_, 0);
v_k_797_ = lean_ctor_get(v_l_623_, 1);
v_v_798_ = lean_ctor_get(v_l_623_, 2);
v_l_799_ = lean_ctor_get(v_l_623_, 3);
v_r_800_ = lean_ctor_get(v_l_623_, 4);
lean_inc(v_r_800_);
v_size_801_ = lean_ctor_get(v_r_624_, 0);
v_k_802_ = lean_ctor_get(v_r_624_, 1);
v_v_803_ = lean_ctor_get(v_r_624_, 2);
v_l_804_ = lean_ctor_get(v_r_624_, 3);
lean_inc(v_l_804_);
v_r_805_ = lean_ctor_get(v_r_624_, 4);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_dec_lt(v_size_796_, v_size_801_);
if (v___x_807_ == 0)
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_943_; 
lean_inc(v_l_799_);
lean_inc(v_v_798_);
lean_inc(v_k_797_);
v_isSharedCheck_943_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; lean_object* v_unused_948_; 
v_unused_944_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_l_623_, 2);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_l_623_, 1);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_948_);
v___x_809_ = v_l_623_;
v_isShared_810_ = v_isSharedCheck_943_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_l_623_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_943_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v_tree_812_; 
v___x_811_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_797_, v_v_798_, v_l_799_, v_r_800_);
v_tree_812_ = lean_ctor_get(v___x_811_, 2);
if (lean_obj_tag(v_tree_812_) == 0)
{
lean_object* v_k_813_; lean_object* v_v_814_; lean_object* v_size_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
lean_inc_ref(v_tree_812_);
v_k_813_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_k_813_);
v_v_814_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_v_814_);
lean_dec_ref(v___x_811_);
v_size_815_ = lean_ctor_get(v_tree_812_, 0);
v___x_816_ = lean_unsigned_to_nat(3u);
v___x_817_ = lean_nat_mul(v___x_816_, v_size_815_);
v___x_818_ = lean_nat_dec_lt(v___x_817_, v_size_801_);
lean_dec(v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_l_804_);
v___x_819_ = lean_nat_add(v___x_806_, v_size_815_);
v___x_820_ = lean_nat_add(v___x_819_, v_size_801_);
lean_dec(v___x_819_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v_r_624_);
lean_ctor_set(v___x_809_, 3, v_tree_812_);
lean_ctor_set(v___x_809_, 2, v_v_814_);
lean_ctor_set(v___x_809_, 1, v_k_813_);
lean_ctor_set(v___x_809_, 0, v___x_820_);
v___x_822_ = v___x_809_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_tree_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_r_624_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_878_; 
lean_inc(v_r_805_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_inc(v_size_801_);
v_isSharedCheck_878_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_879_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_r_624_, 2);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_r_624_, 1);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_883_);
v___x_825_ = v_r_624_;
v_isShared_826_ = v_isSharedCheck_878_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_r_624_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_878_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_size_827_; lean_object* v_k_828_; lean_object* v_v_829_; lean_object* v_l_830_; lean_object* v_r_831_; lean_object* v_size_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_size_827_ = lean_ctor_get(v_l_804_, 0);
v_k_828_ = lean_ctor_get(v_l_804_, 1);
v_v_829_ = lean_ctor_get(v_l_804_, 2);
v_l_830_ = lean_ctor_get(v_l_804_, 3);
v_r_831_ = lean_ctor_get(v_l_804_, 4);
v_size_832_ = lean_ctor_get(v_r_805_, 0);
v___x_833_ = lean_unsigned_to_nat(2u);
v___x_834_ = lean_nat_mul(v___x_833_, v_size_832_);
v___x_835_ = lean_nat_dec_lt(v_size_827_, v___x_834_);
lean_dec(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_863_; 
lean_inc(v_r_831_);
lean_inc(v_l_830_);
lean_inc(v_v_829_);
lean_inc(v_k_828_);
v_isSharedCheck_863_ = !lean_is_exclusive(v_l_804_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; lean_object* v_unused_868_; 
v_unused_864_ = lean_ctor_get(v_l_804_, 4);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_l_804_, 3);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_l_804_, 2);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_l_804_, 1);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_l_804_, 0);
lean_dec(v_unused_868_);
v___x_837_ = v_l_804_;
v_isShared_838_ = v_isSharedCheck_863_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_l_804_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_863_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_853_; 
v___x_839_ = lean_nat_add(v___x_806_, v_size_815_);
v___x_840_ = lean_nat_add(v___x_839_, v_size_801_);
lean_dec(v_size_801_);
if (lean_obj_tag(v_l_830_) == 0)
{
lean_object* v_size_861_; 
v_size_861_ = lean_ctor_get(v_l_830_, 0);
lean_inc(v_size_861_);
v___y_853_ = v_size_861_;
goto v___jp_852_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___y_853_ = v___x_862_;
goto v___jp_852_;
}
v___jp_841_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_nat_add(v___y_842_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___y_842_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_r_805_);
lean_ctor_set(v___x_837_, 3, v_r_831_);
lean_ctor_set(v___x_837_, 2, v_v_803_);
lean_ctor_set(v___x_837_, 1, v_k_802_);
lean_ctor_set(v___x_837_, 0, v___x_845_);
v___x_847_ = v___x_837_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_r_831_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_r_805_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 4, v___x_847_);
lean_ctor_set(v___x_825_, 3, v___y_843_);
lean_ctor_set(v___x_825_, 2, v_v_829_);
lean_ctor_set(v___x_825_, 1, v_k_828_);
lean_ctor_set(v___x_825_, 0, v___x_840_);
v___x_849_ = v___x_825_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_828_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_829_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v___y_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_nat_add(v___x_839_, v___y_853_);
lean_dec(v___y_853_);
lean_dec(v___x_839_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v_l_830_);
lean_ctor_set(v___x_809_, 3, v_tree_812_);
lean_ctor_set(v___x_809_, 2, v_v_814_);
lean_ctor_set(v___x_809_, 1, v_k_813_);
lean_ctor_set(v___x_809_, 0, v___x_854_);
v___x_856_ = v___x_809_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_k_813_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_v_814_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_tree_812_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v_l_830_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = lean_nat_add(v___x_806_, v_size_832_);
if (lean_obj_tag(v_r_831_) == 0)
{
lean_object* v_size_858_; 
v_size_858_ = lean_ctor_get(v_r_831_, 0);
lean_inc(v_size_858_);
v___y_842_ = v___x_857_;
v___y_843_ = v___x_856_;
v___y_844_ = v_size_858_;
goto v___jp_841_;
}
else
{
lean_object* v___x_859_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___y_842_ = v___x_857_;
v___y_843_ = v___x_856_;
v___y_844_ = v___x_859_;
goto v___jp_841_;
}
}
}
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_869_ = lean_nat_add(v___x_806_, v_size_815_);
v___x_870_ = lean_nat_add(v___x_869_, v_size_801_);
lean_dec(v_size_801_);
v___x_871_ = lean_nat_add(v___x_869_, v_size_827_);
lean_dec(v___x_869_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 4, v_l_804_);
lean_ctor_set(v___x_825_, 3, v_tree_812_);
lean_ctor_set(v___x_825_, 2, v_v_814_);
lean_ctor_set(v___x_825_, 1, v_k_813_);
lean_ctor_set(v___x_825_, 0, v___x_871_);
v___x_873_ = v___x_825_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_k_813_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_v_814_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_tree_812_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_l_804_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v_r_805_);
lean_ctor_set(v___x_809_, 3, v___x_873_);
lean_ctor_set(v___x_809_, 2, v_v_803_);
lean_ctor_set(v___x_809_, 1, v_k_802_);
lean_ctor_set(v___x_809_, 0, v___x_870_);
v___x_875_ = v___x_809_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_r_805_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
else
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_937_; 
lean_inc(v_r_805_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_inc(v_size_801_);
v_isSharedCheck_937_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; lean_object* v_unused_939_; lean_object* v_unused_940_; lean_object* v_unused_941_; lean_object* v_unused_942_; 
v_unused_938_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_r_624_, 2);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_r_624_, 1);
lean_dec(v_unused_941_);
v_unused_942_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_942_);
v___x_885_ = v_r_624_;
v_isShared_886_ = v_isSharedCheck_937_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_r_624_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_937_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
if (lean_obj_tag(v_l_804_) == 0)
{
if (lean_obj_tag(v_r_805_) == 0)
{
lean_object* v_k_887_; lean_object* v_v_888_; lean_object* v_size_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_inc(v_tree_812_);
v_k_887_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_k_887_);
v_v_888_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_v_888_);
lean_dec_ref(v___x_811_);
v_size_889_ = lean_ctor_get(v_l_804_, 0);
v___x_890_ = lean_nat_add(v___x_806_, v_size_801_);
lean_dec(v_size_801_);
v___x_891_ = lean_nat_add(v___x_806_, v_size_889_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 4, v_l_804_);
lean_ctor_set(v___x_885_, 3, v_tree_812_);
lean_ctor_set(v___x_885_, 2, v_v_888_);
lean_ctor_set(v___x_885_, 1, v_k_887_);
lean_ctor_set(v___x_885_, 0, v___x_891_);
v___x_893_ = v___x_885_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_tree_812_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_l_804_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v_r_805_);
lean_ctor_set(v___x_809_, 3, v___x_893_);
lean_ctor_set(v___x_809_, 2, v_v_803_);
lean_ctor_set(v___x_809_, 1, v_k_802_);
lean_ctor_set(v___x_809_, 0, v___x_890_);
v___x_895_ = v___x_809_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_r_805_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_k_898_; lean_object* v_v_899_; lean_object* v_k_900_; lean_object* v_v_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_size_801_);
v_k_898_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_k_898_);
v_v_899_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_v_899_);
lean_dec_ref(v___x_811_);
v_k_900_ = lean_ctor_get(v_l_804_, 1);
v_v_901_ = lean_ctor_get(v_l_804_, 2);
v_isSharedCheck_915_ = !lean_is_exclusive(v_l_804_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_916_ = lean_ctor_get(v_l_804_, 4);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_l_804_, 3);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_l_804_, 0);
lean_dec(v_unused_918_);
v___x_903_ = v_l_804_;
v_isShared_904_ = v_isSharedCheck_915_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_v_901_);
lean_inc(v_k_900_);
lean_dec(v_l_804_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_915_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_unsigned_to_nat(3u);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 4, v_r_805_);
lean_ctor_set(v___x_903_, 3, v_r_805_);
lean_ctor_set(v___x_903_, 2, v_v_899_);
lean_ctor_set(v___x_903_, 1, v_k_898_);
lean_ctor_set(v___x_903_, 0, v___x_806_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_r_805_);
v___x_907_ = v_reuseFailAlloc_914_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 3, v_r_805_);
lean_ctor_set(v___x_885_, 0, v___x_806_);
v___x_909_ = v___x_885_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_805_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v___x_909_);
lean_ctor_set(v___x_809_, 3, v___x_907_);
lean_ctor_set(v___x_809_, 2, v_v_901_);
lean_ctor_set(v___x_809_, 1, v_k_900_);
lean_ctor_set(v___x_809_, 0, v___x_905_);
v___x_911_ = v___x_809_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_901_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_805_) == 0)
{
lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_size_801_);
v_k_919_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_k_919_);
v_v_920_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_v_920_);
lean_dec_ref(v___x_811_);
v___x_921_ = lean_unsigned_to_nat(3u);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 4, v_l_804_);
lean_ctor_set(v___x_885_, 2, v_v_920_);
lean_ctor_set(v___x_885_, 1, v_k_919_);
lean_ctor_set(v___x_885_, 0, v___x_806_);
v___x_923_ = v___x_885_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_l_804_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v_r_805_);
lean_ctor_set(v___x_809_, 3, v___x_923_);
lean_ctor_set(v___x_809_, 2, v_v_803_);
lean_ctor_set(v___x_809_, 1, v_k_802_);
lean_ctor_set(v___x_809_, 0, v___x_921_);
v___x_925_ = v___x_809_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_r_805_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_k_928_; lean_object* v_v_929_; lean_object* v___x_931_; 
v_k_928_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_k_928_);
v_v_929_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_v_929_);
lean_dec_ref(v___x_811_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 3, v_r_805_);
v___x_931_ = v___x_885_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_size_801_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_r_805_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(2u);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v___x_931_);
lean_ctor_set(v___x_809_, 3, v_r_805_);
lean_ctor_set(v___x_809_, 2, v_v_929_);
lean_ctor_set(v___x_809_, 1, v_k_928_);
lean_ctor_set(v___x_809_, 0, v___x_932_);
v___x_934_ = v___x_809_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_k_928_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_v_929_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v___x_931_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
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
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1101_; 
lean_inc(v_r_805_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; 
v_unused_1102_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_r_624_, 2);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_r_624_, 1);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_1106_);
v___x_950_ = v_r_624_;
v_isShared_951_ = v_isSharedCheck_1101_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_r_624_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1101_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v_tree_953_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_802_, v_v_803_, v_l_804_, v_r_805_);
v_tree_953_ = lean_ctor_get(v___x_952_, 2);
lean_inc(v_tree_953_);
if (lean_obj_tag(v_tree_953_) == 0)
{
lean_object* v_k_954_; lean_object* v_v_955_; lean_object* v_size_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_k_954_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_k_954_);
v_v_955_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_v_955_);
lean_dec_ref(v___x_952_);
v_size_956_ = lean_ctor_get(v_tree_953_, 0);
v___x_957_ = lean_unsigned_to_nat(3u);
v___x_958_ = lean_nat_mul(v___x_957_, v_size_956_);
v___x_959_ = lean_nat_dec_lt(v___x_958_, v_size_796_);
lean_dec(v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v_r_800_);
v___x_960_ = lean_nat_add(v___x_806_, v_size_796_);
v___x_961_ = lean_nat_add(v___x_960_, v_size_956_);
lean_dec(v___x_960_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_tree_953_);
lean_ctor_set(v___x_950_, 3, v_l_623_);
lean_ctor_set(v___x_950_, 2, v_v_955_);
lean_ctor_set(v___x_950_, 1, v_k_954_);
lean_ctor_set(v___x_950_, 0, v___x_961_);
v___x_963_ = v___x_950_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_k_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_v_955_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_l_623_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_tree_953_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1030_; 
lean_inc(v_l_799_);
lean_inc(v_v_798_);
lean_inc(v_k_797_);
lean_inc(v_size_796_);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; 
v_unused_1031_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_l_623_, 2);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_l_623_, 1);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_1035_);
v___x_966_ = v_l_623_;
v_isShared_967_ = v_isSharedCheck_1030_;
goto v_resetjp_965_;
}
else
{
lean_dec(v_l_623_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1030_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_size_968_; lean_object* v_size_969_; lean_object* v_k_970_; lean_object* v_v_971_; lean_object* v_l_972_; lean_object* v_r_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_size_968_ = lean_ctor_get(v_l_799_, 0);
v_size_969_ = lean_ctor_get(v_r_800_, 0);
v_k_970_ = lean_ctor_get(v_r_800_, 1);
v_v_971_ = lean_ctor_get(v_r_800_, 2);
v_l_972_ = lean_ctor_get(v_r_800_, 3);
v_r_973_ = lean_ctor_get(v_r_800_, 4);
v___x_974_ = lean_unsigned_to_nat(2u);
v___x_975_ = lean_nat_mul(v___x_974_, v_size_968_);
v___x_976_ = lean_nat_dec_lt(v_size_969_, v___x_975_);
lean_dec(v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1014_; 
lean_inc(v_r_973_);
lean_inc(v_l_972_);
lean_inc(v_v_971_);
lean_inc(v_k_970_);
lean_del_object(v___x_966_);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_r_800_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1015_ = lean_ctor_get(v_r_800_, 4);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_r_800_, 3);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_800_, 2);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_800_, 1);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_r_800_, 0);
lean_dec(v_unused_1019_);
v___x_978_ = v_r_800_;
v_isShared_979_ = v_isSharedCheck_1014_;
goto v_resetjp_977_;
}
else
{
lean_dec(v_r_800_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1014_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___x_1002_; lean_object* v___y_1004_; 
v___x_980_ = lean_nat_add(v___x_806_, v_size_796_);
lean_dec(v_size_796_);
v___x_981_ = lean_nat_add(v___x_980_, v_size_956_);
lean_dec(v___x_980_);
v___x_1002_ = lean_nat_add(v___x_806_, v_size_968_);
if (lean_obj_tag(v_l_972_) == 0)
{
lean_object* v_size_1012_; 
v_size_1012_ = lean_ctor_get(v_l_972_, 0);
lean_inc(v_size_1012_);
v___y_1004_ = v_size_1012_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___y_1004_ = v___x_1013_;
goto v___jp_1003_;
}
v___jp_982_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_nat_add(v___y_983_, v___y_985_);
lean_dec(v___y_985_);
lean_dec(v___y_983_);
lean_inc_ref(v_tree_953_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 4, v_tree_953_);
lean_ctor_set(v___x_978_, 3, v_r_973_);
lean_ctor_set(v___x_978_, 2, v_v_955_);
lean_ctor_set(v___x_978_, 1, v_k_954_);
lean_ctor_set(v___x_978_, 0, v___x_986_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_954_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_955_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_r_973_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_tree_953_);
v___x_988_ = v_reuseFailAlloc_1001_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_isSharedCheck_995_ = !lean_is_exclusive(v_tree_953_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_996_ = lean_ctor_get(v_tree_953_, 4);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_tree_953_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_tree_953_, 2);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_tree_953_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_tree_953_, 0);
lean_dec(v_unused_1000_);
v___x_990_ = v_tree_953_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_dec(v_tree_953_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 4, v___x_988_);
lean_ctor_set(v___x_990_, 3, v___y_984_);
lean_ctor_set(v___x_990_, 2, v_v_971_);
lean_ctor_set(v___x_990_, 1, v_k_970_);
lean_ctor_set(v___x_990_, 0, v___x_981_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_970_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_971_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v___y_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v___x_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
v___jp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_nat_add(v___x_1002_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec(v___x_1002_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_l_972_);
lean_ctor_set(v___x_950_, 3, v_l_799_);
lean_ctor_set(v___x_950_, 2, v_v_798_);
lean_ctor_set(v___x_950_, 1, v_k_797_);
lean_ctor_set(v___x_950_, 0, v___x_1005_);
v___x_1007_ = v___x_950_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_l_799_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_l_972_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_nat_add(v___x_806_, v_size_956_);
if (lean_obj_tag(v_r_973_) == 0)
{
lean_object* v_size_1009_; 
v_size_1009_ = lean_ctor_get(v_r_973_, 0);
lean_inc(v_size_1009_);
v___y_983_ = v___x_1008_;
v___y_984_ = v___x_1007_;
v___y_985_ = v_size_1009_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_unsigned_to_nat(0u);
v___y_983_ = v___x_1008_;
v___y_984_ = v___x_1007_;
v___y_985_ = v___x_1010_;
goto v___jp_982_;
}
}
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1020_ = lean_nat_add(v___x_806_, v_size_796_);
lean_dec(v_size_796_);
v___x_1021_ = lean_nat_add(v___x_1020_, v_size_956_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_nat_add(v___x_806_, v_size_956_);
v___x_1023_ = lean_nat_add(v___x_1022_, v_size_969_);
lean_dec(v___x_1022_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_tree_953_);
lean_ctor_set(v___x_950_, 3, v_r_800_);
lean_ctor_set(v___x_950_, 2, v_v_955_);
lean_ctor_set(v___x_950_, 1, v_k_954_);
lean_ctor_set(v___x_950_, 0, v___x_1023_);
v___x_1025_ = v___x_950_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_k_954_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_v_955_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_r_800_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_tree_953_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 4, v___x_1025_);
lean_ctor_set(v___x_966_, 0, v___x_1021_);
v___x_1027_ = v___x_966_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_l_799_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_799_) == 0)
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1059_; 
lean_inc_ref(v_l_799_);
lean_inc(v_v_798_);
lean_inc(v_k_797_);
lean_inc(v_size_796_);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; lean_object* v_unused_1063_; lean_object* v_unused_1064_; 
v_unused_1060_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_l_623_, 2);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_l_623_, 1);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_1064_);
v___x_1037_ = v_l_623_;
v_isShared_1038_ = v_isSharedCheck_1059_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v_l_623_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1059_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
if (lean_obj_tag(v_r_800_) == 0)
{
lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v_size_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v_k_1039_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_k_1039_);
v_v_1040_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_v_1040_);
lean_dec_ref(v___x_952_);
v_size_1041_ = lean_ctor_get(v_r_800_, 0);
v___x_1042_ = lean_nat_add(v___x_806_, v_size_796_);
lean_dec(v_size_796_);
v___x_1043_ = lean_nat_add(v___x_806_, v_size_1041_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_tree_953_);
lean_ctor_set(v___x_950_, 3, v_r_800_);
lean_ctor_set(v___x_950_, 2, v_v_1040_);
lean_ctor_set(v___x_950_, 1, v_k_1039_);
lean_ctor_set(v___x_950_, 0, v___x_1043_);
v___x_1045_ = v___x_950_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_r_800_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_tree_953_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 4, v___x_1045_);
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1047_ = v___x_1037_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_l_799_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_k_1050_; lean_object* v_v_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_dec(v_size_796_);
v_k_1050_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_k_1050_);
v_v_1051_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_v_1051_);
lean_dec_ref(v___x_952_);
v___x_1052_ = lean_unsigned_to_nat(3u);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_r_800_);
lean_ctor_set(v___x_950_, 3, v_r_800_);
lean_ctor_set(v___x_950_, 2, v_v_1051_);
lean_ctor_set(v___x_950_, 1, v_k_1050_);
lean_ctor_set(v___x_950_, 0, v___x_806_);
v___x_1054_ = v___x_950_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_k_1050_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_v_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_r_800_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_r_800_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 4, v___x_1054_);
lean_ctor_set(v___x_1037_, 0, v___x_1052_);
v___x_1056_ = v___x_1037_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_l_799_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_800_) == 0)
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1089_; 
lean_inc(v_l_799_);
lean_inc(v_v_798_);
lean_inc(v_k_797_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_l_623_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1090_ = lean_ctor_get(v_l_623_, 4);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_l_623_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_l_623_, 2);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_623_, 1);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_623_, 0);
lean_dec(v_unused_1094_);
v___x_1066_ = v_l_623_;
v_isShared_1067_ = v_isSharedCheck_1089_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v_l_623_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1089_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_k_1068_; lean_object* v_v_1069_; lean_object* v_k_1070_; lean_object* v_v_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1085_; 
v_k_1068_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_k_1068_);
v_v_1069_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_v_1069_);
lean_dec_ref(v___x_952_);
v_k_1070_ = lean_ctor_get(v_r_800_, 1);
v_v_1071_ = lean_ctor_get(v_r_800_, 2);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_r_800_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; lean_object* v_unused_1088_; 
v_unused_1086_ = lean_ctor_get(v_r_800_, 4);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_r_800_, 3);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_r_800_, 0);
lean_dec(v_unused_1088_);
v___x_1073_ = v_r_800_;
v_isShared_1074_ = v_isSharedCheck_1085_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_v_1071_);
lean_inc(v_k_1070_);
lean_dec(v_r_800_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1085_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_unsigned_to_nat(3u);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 4, v_l_799_);
lean_ctor_set(v___x_1073_, 3, v_l_799_);
lean_ctor_set(v___x_1073_, 2, v_v_798_);
lean_ctor_set(v___x_1073_, 1, v_k_797_);
lean_ctor_set(v___x_1073_, 0, v___x_806_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_l_799_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v_l_799_);
v___x_1077_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_l_799_);
lean_ctor_set(v___x_950_, 3, v_l_799_);
lean_ctor_set(v___x_950_, 2, v_v_1069_);
lean_ctor_set(v___x_950_, 1, v_k_1068_);
lean_ctor_set(v___x_950_, 0, v___x_806_);
v___x_1079_ = v___x_950_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_1068_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_1069_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_l_799_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_l_799_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 4, v___x_1079_);
lean_ctor_set(v___x_1066_, 3, v___x_1077_);
lean_ctor_set(v___x_1066_, 2, v_v_1071_);
lean_ctor_set(v___x_1066_, 1, v_k_1070_);
lean_ctor_set(v___x_1066_, 0, v___x_1075_);
v___x_1081_ = v___x_1066_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_k_1070_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_v_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
else
{
lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v_k_1095_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_k_1095_);
v_v_1096_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_v_1096_);
lean_dec_ref(v___x_952_);
v___x_1097_ = lean_unsigned_to_nat(2u);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_r_800_);
lean_ctor_set(v___x_950_, 3, v_l_623_);
lean_ctor_set(v___x_950_, 2, v_v_1096_);
lean_ctor_set(v___x_950_, 1, v_k_1095_);
lean_ctor_set(v___x_950_, 0, v___x_1097_);
v___x_1099_ = v___x_950_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_l_623_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v_r_800_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
else
{
return v_l_623_;
}
}
else
{
return v_r_624_;
}
}
}
else
{
lean_object* v_impl_1107_; lean_object* v___x_1108_; 
v_impl_1107_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_619_, v_l_623_);
v___x_1108_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1107_) == 0)
{
if (lean_obj_tag(v_r_624_) == 0)
{
lean_object* v_size_1109_; lean_object* v_size_1110_; lean_object* v_k_1111_; lean_object* v_v_1112_; lean_object* v_l_1113_; lean_object* v_r_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_size_1109_ = lean_ctor_get(v_impl_1107_, 0);
v_size_1110_ = lean_ctor_get(v_r_624_, 0);
v_k_1111_ = lean_ctor_get(v_r_624_, 1);
v_v_1112_ = lean_ctor_get(v_r_624_, 2);
v_l_1113_ = lean_ctor_get(v_r_624_, 3);
lean_inc(v_l_1113_);
v_r_1114_ = lean_ctor_get(v_r_624_, 4);
v___x_1115_ = lean_unsigned_to_nat(3u);
v___x_1116_ = lean_nat_mul(v___x_1115_, v_size_1109_);
v___x_1117_ = lean_nat_dec_lt(v___x_1116_, v_size_1110_);
lean_dec(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_dec(v_l_1113_);
v___x_1118_ = lean_nat_add(v___x_1108_, v_size_1109_);
v___x_1119_ = lean_nat_add(v___x_1118_, v_size_1110_);
lean_dec(v___x_1118_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 3, v_impl_1107_);
lean_ctor_set(v___x_626_, 0, v___x_1119_);
v___x_1121_ = v___x_626_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_impl_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_r_624_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
else
{
lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1186_; 
lean_inc(v_r_1114_);
lean_inc(v_v_1112_);
lean_inc(v_k_1111_);
lean_inc(v_size_1110_);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; lean_object* v_unused_1191_; 
v_unused_1187_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_r_624_, 2);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_r_624_, 1);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_1191_);
v___x_1124_ = v_r_624_;
v_isShared_1125_ = v_isSharedCheck_1186_;
goto v_resetjp_1123_;
}
else
{
lean_dec(v_r_624_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1186_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_size_1126_; lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v_l_1129_; lean_object* v_r_1130_; lean_object* v_size_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_size_1126_ = lean_ctor_get(v_l_1113_, 0);
v_k_1127_ = lean_ctor_get(v_l_1113_, 1);
v_v_1128_ = lean_ctor_get(v_l_1113_, 2);
v_l_1129_ = lean_ctor_get(v_l_1113_, 3);
v_r_1130_ = lean_ctor_get(v_l_1113_, 4);
v_size_1131_ = lean_ctor_get(v_r_1114_, 0);
v___x_1132_ = lean_unsigned_to_nat(2u);
v___x_1133_ = lean_nat_mul(v___x_1132_, v_size_1131_);
v___x_1134_ = lean_nat_dec_lt(v_size_1126_, v___x_1133_);
lean_dec(v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1162_; 
lean_inc(v_r_1130_);
lean_inc(v_l_1129_);
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_l_1113_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; 
v_unused_1163_ = lean_ctor_get(v_l_1113_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_l_1113_, 3);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_l_1113_, 2);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_l_1113_, 1);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_l_1113_, 0);
lean_dec(v_unused_1167_);
v___x_1136_ = v_l_1113_;
v_isShared_1137_ = v_isSharedCheck_1162_;
goto v_resetjp_1135_;
}
else
{
lean_dec(v_l_1113_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1162_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1152_; 
v___x_1138_ = lean_nat_add(v___x_1108_, v_size_1109_);
v___x_1139_ = lean_nat_add(v___x_1138_, v_size_1110_);
lean_dec(v_size_1110_);
if (lean_obj_tag(v_l_1129_) == 0)
{
lean_object* v_size_1160_; 
v_size_1160_ = lean_ctor_get(v_l_1129_, 0);
lean_inc(v_size_1160_);
v___y_1152_ = v_size_1160_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___y_1152_ = v___x_1161_;
goto v___jp_1151_;
}
v___jp_1140_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_nat_add(v___y_1141_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec(v___y_1141_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 4, v_r_1114_);
lean_ctor_set(v___x_1136_, 3, v_r_1130_);
lean_ctor_set(v___x_1136_, 2, v_v_1112_);
lean_ctor_set(v___x_1136_, 1, v_k_1111_);
lean_ctor_set(v___x_1136_, 0, v___x_1144_);
v___x_1146_ = v___x_1136_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_1111_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_1112_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_r_1130_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_r_1114_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 4, v___x_1146_);
lean_ctor_set(v___x_1124_, 3, v___y_1142_);
lean_ctor_set(v___x_1124_, 2, v_v_1128_);
lean_ctor_set(v___x_1124_, 1, v_k_1127_);
lean_ctor_set(v___x_1124_, 0, v___x_1139_);
v___x_1148_ = v___x_1124_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v___y_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_nat_add(v___x_1138_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec(v___x_1138_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_l_1129_);
lean_ctor_set(v___x_626_, 3, v_impl_1107_);
lean_ctor_set(v___x_626_, 0, v___x_1153_);
v___x_1155_ = v___x_626_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_impl_1107_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_l_1129_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_nat_add(v___x_1108_, v_size_1131_);
if (lean_obj_tag(v_r_1130_) == 0)
{
lean_object* v_size_1157_; 
v_size_1157_ = lean_ctor_get(v_r_1130_, 0);
lean_inc(v_size_1157_);
v___y_1141_ = v___x_1156_;
v___y_1142_ = v___x_1155_;
v___y_1143_ = v_size_1157_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_unsigned_to_nat(0u);
v___y_1141_ = v___x_1156_;
v___y_1142_ = v___x_1155_;
v___y_1143_ = v___x_1158_;
goto v___jp_1140_;
}
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
lean_del_object(v___x_626_);
v___x_1168_ = lean_nat_add(v___x_1108_, v_size_1109_);
v___x_1169_ = lean_nat_add(v___x_1168_, v_size_1110_);
lean_dec(v_size_1110_);
v___x_1170_ = lean_nat_add(v___x_1168_, v_size_1126_);
lean_dec(v___x_1168_);
lean_inc_ref(v_impl_1107_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 4, v_l_1113_);
lean_ctor_set(v___x_1124_, 3, v_impl_1107_);
lean_ctor_set(v___x_1124_, 2, v_v_622_);
lean_ctor_set(v___x_1124_, 1, v_k_621_);
lean_ctor_set(v___x_1124_, 0, v___x_1170_);
v___x_1172_ = v___x_1124_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_impl_1107_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_l_1113_);
v___x_1172_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_isSharedCheck_1179_ = !lean_is_exclusive(v_impl_1107_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; lean_object* v_unused_1184_; 
v_unused_1180_ = lean_ctor_get(v_impl_1107_, 4);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_impl_1107_, 3);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_impl_1107_, 2);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_impl_1107_, 1);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_impl_1107_, 0);
lean_dec(v_unused_1184_);
v___x_1174_ = v_impl_1107_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_impl_1107_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v_r_1114_);
lean_ctor_set(v___x_1174_, 3, v___x_1172_);
lean_ctor_set(v___x_1174_, 2, v_v_1112_);
lean_ctor_set(v___x_1174_, 1, v_k_1111_);
lean_ctor_set(v___x_1174_, 0, v___x_1169_);
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_k_1111_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_v_1112_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v_r_1114_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v_size_1192_ = lean_ctor_get(v_impl_1107_, 0);
v___x_1193_ = lean_nat_add(v___x_1108_, v_size_1192_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 3, v_impl_1107_);
lean_ctor_set(v___x_626_, 0, v___x_1193_);
v___x_1195_ = v___x_626_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_impl_1107_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_r_624_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
if (lean_obj_tag(v_r_624_) == 0)
{
lean_object* v_l_1197_; 
v_l_1197_ = lean_ctor_get(v_r_624_, 3);
lean_inc(v_l_1197_);
if (lean_obj_tag(v_l_1197_) == 0)
{
lean_object* v_r_1198_; 
v_r_1198_ = lean_ctor_get(v_r_624_, 4);
lean_inc(v_r_1198_);
if (lean_obj_tag(v_r_1198_) == 0)
{
lean_object* v_size_1199_; lean_object* v_k_1200_; lean_object* v_v_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1214_; 
v_size_1199_ = lean_ctor_get(v_r_624_, 0);
v_k_1200_ = lean_ctor_get(v_r_624_, 1);
v_v_1201_ = lean_ctor_get(v_r_624_, 2);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; lean_object* v_unused_1216_; 
v_unused_1215_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_1216_);
v___x_1203_ = v_r_624_;
v_isShared_1204_ = v_isSharedCheck_1214_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_v_1201_);
lean_inc(v_k_1200_);
lean_inc(v_size_1199_);
lean_dec(v_r_624_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1214_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_size_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v_size_1205_ = lean_ctor_get(v_l_1197_, 0);
v___x_1206_ = lean_nat_add(v___x_1108_, v_size_1199_);
lean_dec(v_size_1199_);
v___x_1207_ = lean_nat_add(v___x_1108_, v_size_1205_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v_l_1197_);
lean_ctor_set(v___x_1203_, 3, v_impl_1107_);
lean_ctor_set(v___x_1203_, 2, v_v_622_);
lean_ctor_set(v___x_1203_, 1, v_k_621_);
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_impl_1107_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_l_1197_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_r_1198_);
lean_ctor_set(v___x_626_, 3, v___x_1209_);
lean_ctor_set(v___x_626_, 2, v_v_1201_);
lean_ctor_set(v___x_626_, 1, v_k_1200_);
lean_ctor_set(v___x_626_, 0, v___x_1206_);
v___x_1211_ = v___x_626_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_k_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_v_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_r_1198_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1241_; 
v_k_1217_ = lean_ctor_get(v_r_624_, 1);
v_v_1218_ = lean_ctor_get(v_r_624_, 2);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; lean_object* v_unused_1243_; lean_object* v_unused_1244_; 
v_unused_1242_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_1243_);
v_unused_1244_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_1244_);
v___x_1220_ = v_r_624_;
v_isShared_1221_ = v_isSharedCheck_1241_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
lean_dec(v_r_624_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1241_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_k_1222_; lean_object* v_v_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1237_; 
v_k_1222_ = lean_ctor_get(v_l_1197_, 1);
v_v_1223_ = lean_ctor_get(v_l_1197_, 2);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_l_1197_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; 
v_unused_1238_ = lean_ctor_get(v_l_1197_, 4);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_l_1197_, 3);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_l_1197_, 0);
lean_dec(v_unused_1240_);
v___x_1225_ = v_l_1197_;
v_isShared_1226_ = v_isSharedCheck_1237_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_v_1223_);
lean_inc(v_k_1222_);
lean_dec(v_l_1197_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1237_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_unsigned_to_nat(3u);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 4, v_r_1198_);
lean_ctor_set(v___x_1225_, 3, v_r_1198_);
lean_ctor_set(v___x_1225_, 2, v_v_622_);
lean_ctor_set(v___x_1225_, 1, v_k_621_);
lean_ctor_set(v___x_1225_, 0, v___x_1108_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_r_1198_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_r_1198_);
v___x_1229_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 3, v_r_1198_);
lean_ctor_set(v___x_1220_, 0, v___x_1108_);
v___x_1231_ = v___x_1220_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_r_1198_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_r_1198_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v___x_1231_);
lean_ctor_set(v___x_626_, 3, v___x_1229_);
lean_ctor_set(v___x_626_, 2, v_v_1223_);
lean_ctor_set(v___x_626_, 1, v_k_1222_);
lean_ctor_set(v___x_626_, 0, v___x_1227_);
v___x_1233_ = v___x_626_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1245_; 
v_r_1245_ = lean_ctor_get(v_r_624_, 4);
lean_inc(v_r_1245_);
if (lean_obj_tag(v_r_1245_) == 0)
{
lean_object* v_k_1246_; lean_object* v_v_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1258_; 
v_k_1246_ = lean_ctor_get(v_r_624_, 1);
v_v_1247_ = lean_ctor_get(v_r_624_, 2);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; lean_object* v_unused_1261_; 
v_unused_1259_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_1260_);
v_unused_1261_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_1261_);
v___x_1249_ = v_r_624_;
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_v_1247_);
lean_inc(v_k_1246_);
lean_dec(v_r_624_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_unsigned_to_nat(3u);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 4, v_l_1197_);
lean_ctor_set(v___x_1249_, 2, v_v_622_);
lean_ctor_set(v___x_1249_, 1, v_k_621_);
lean_ctor_set(v___x_1249_, 0, v___x_1108_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_l_1197_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_r_1245_);
lean_ctor_set(v___x_626_, 3, v___x_1253_);
lean_ctor_set(v___x_626_, 2, v_v_1247_);
lean_ctor_set(v___x_626_, 1, v_k_1246_);
lean_ctor_set(v___x_626_, 0, v___x_1251_);
v___x_1255_ = v___x_626_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_1247_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_r_1245_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_size_1262_; lean_object* v_k_1263_; lean_object* v_v_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1275_; 
v_size_1262_ = lean_ctor_get(v_r_624_, 0);
v_k_1263_ = lean_ctor_get(v_r_624_, 1);
v_v_1264_ = lean_ctor_get(v_r_624_, 2);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; lean_object* v_unused_1277_; 
v_unused_1276_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_1276_);
v_unused_1277_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_1277_);
v___x_1266_ = v_r_624_;
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_v_1264_);
lean_inc(v_k_1263_);
lean_inc(v_size_1262_);
lean_dec(v_r_624_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 3, v_r_1245_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_size_1262_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_k_1263_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_v_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_r_1245_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_r_1245_);
v___x_1269_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_unsigned_to_nat(2u);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v___x_1269_);
lean_ctor_set(v___x_626_, 3, v_r_1245_);
lean_ctor_set(v___x_626_, 0, v___x_1270_);
v___x_1272_ = v___x_626_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_r_1245_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v___x_1269_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
else
{
lean_object* v___x_1279_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 3, v_r_624_);
lean_ctor_set(v___x_626_, 0, v___x_1108_);
v___x_1279_ = v___x_626_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_r_624_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_r_624_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
else
{
return v_t_620_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_619_ = stack[0].m_num;
lean_object* v_t_620_ = stack[1].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_619_, v_t_620_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg___boxed(lean_object* v_k_1284_, lean_object* v_t_1285_){
_start:
{
uint64_t v_k_boxed_1286_; lean_object* v_res_1287_; 
v_k_boxed_1286_ = lean_unbox_uint64(v_k_1284_);
lean_dec_ref(v_k_1284_);
v_res_1287_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_boxed_1286_, v_t_1285_);
return v_res_1287_;
}
}
lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t v_h_1288_, lean_object* v_st_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_h_1288_, v_st_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT void l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_1288_ = stack[0].m_num;
lean_object* v_st_1289_ = stack[1].m_obj;
lean_object* v_res_1291_;
v_res_1291_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_1288_, v_st_1289_);
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object* v_h_1292_, lean_object* v_st_1293_){
_start:
{
uint64_t v_h_boxed_1294_; lean_object* v_res_1295_; 
v_h_boxed_1294_ = lean_unbox_uint64(v_h_1292_);
lean_dec_ref(v_h_1292_);
v_res_1295_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_1294_, v_st_1293_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_ctor_set(v___x_1302_, 2, v___x_1301_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
lean_ctor_set(v___x_1302_, 4, v___x_1301_);
lean_ctor_set(v___x_1302_, 5, v___x_1301_);
return v___x_1302_;
}
}
lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v_env_1310_; lean_object* v_nextMacroScope_1311_; lean_object* v_ngen_1312_; lean_object* v_auxDeclNGen_1313_; lean_object* v_traceState_1314_; lean_object* v_recordedDeps_1315_; lean_object* v_messages_1316_; lean_object* v_infoState_1317_; lean_object* v_snapshotTasks_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1346_; 
v___x_1307_ = lean_box_uint64(v_h_1303_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1308_, 0, v___x_1307_);
v___x_1309_ = lean_st_ref_take(v___y_1305_);
v_env_1310_ = lean_ctor_get(v___x_1309_, 0);
v_nextMacroScope_1311_ = lean_ctor_get(v___x_1309_, 1);
v_ngen_1312_ = lean_ctor_get(v___x_1309_, 2);
v_auxDeclNGen_1313_ = lean_ctor_get(v___x_1309_, 3);
v_traceState_1314_ = lean_ctor_get(v___x_1309_, 4);
v_recordedDeps_1315_ = lean_ctor_get(v___x_1309_, 6);
v_messages_1316_ = lean_ctor_get(v___x_1309_, 7);
v_infoState_1317_ = lean_ctor_get(v___x_1309_, 8);
v_snapshotTasks_1318_ = lean_ctor_get(v___x_1309_, 9);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1309_, 5);
lean_dec(v_unused_1347_);
v___x_1320_ = v___x_1309_;
v_isShared_1321_ = v_isSharedCheck_1346_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_snapshotTasks_1318_);
lean_inc(v_infoState_1317_);
lean_inc(v_messages_1316_);
lean_inc(v_recordedDeps_1315_);
lean_inc(v_traceState_1314_);
lean_inc(v_auxDeclNGen_1313_);
lean_inc(v_ngen_1312_);
lean_inc(v_nextMacroScope_1311_);
lean_inc(v_env_1310_);
lean_dec(v___x_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1346_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1322_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1323_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1322_, v_env_1310_, v___f_1308_);
v___x_1324_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 5, v___x_1324_);
lean_ctor_set(v___x_1320_, 0, v___x_1323_);
v___x_1326_ = v___x_1320_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_nextMacroScope_1311_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_ngen_1312_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_auxDeclNGen_1313_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_traceState_1314_);
lean_ctor_set(v_reuseFailAlloc_1345_, 5, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1345_, 6, v_recordedDeps_1315_);
lean_ctor_set(v_reuseFailAlloc_1345_, 7, v_messages_1316_);
lean_ctor_set(v_reuseFailAlloc_1345_, 8, v_infoState_1317_);
lean_ctor_set(v_reuseFailAlloc_1345_, 9, v_snapshotTasks_1318_);
v___x_1326_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_mctx_1329_; lean_object* v_zetaDeltaFVarIds_1330_; lean_object* v_postponed_1331_; lean_object* v_diag_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1343_; 
v___x_1327_ = lean_st_ref_put(v___y_1305_, v___x_1326_);
v___x_1328_ = lean_st_ref_take(v___y_1304_);
v_mctx_1329_ = lean_ctor_get(v___x_1328_, 0);
v_zetaDeltaFVarIds_1330_ = lean_ctor_get(v___x_1328_, 2);
v_postponed_1331_ = lean_ctor_get(v___x_1328_, 3);
v_diag_1332_ = lean_ctor_get(v___x_1328_, 4);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1328_, 1);
lean_dec(v_unused_1344_);
v___x_1334_ = v___x_1328_;
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_diag_1332_);
lean_inc(v_postponed_1331_);
lean_inc(v_zetaDeltaFVarIds_1330_);
lean_inc(v_mctx_1329_);
lean_dec(v___x_1328_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_mctx_1329_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_zetaDeltaFVarIds_1330_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_postponed_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_diag_1332_);
v___x_1339_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_st_ref_put(v___y_1304_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1336_);
return v___x_1341_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_1303_ = stack[0].m_num;
lean_object* v___y_1304_ = stack[1].m_obj;
lean_object* v___y_1305_ = stack[2].m_obj;
lean_object* v_res_1348_;
v_res_1348_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_1303_, v___y_1304_, v___y_1305_);
stack->m_obj
 = v_res_1348_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint64_t v_h_boxed_1353_; lean_object* v_res_1354_; 
v_h_boxed_1353_ = lean_unbox_uint64(v_h_1349_);
lean_dec_ref(v_h_1349_);
v_res_1354_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1353_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
return v_res_1354_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1355_, uint64_t v_k_1356_, lean_object* v_fallback_1357_){
_start:
{
if (lean_obj_tag(v_t_1355_) == 0)
{
lean_object* v_k_1358_; lean_object* v_v_1359_; lean_object* v_l_1360_; lean_object* v_r_1361_; uint64_t v___x_1362_; uint8_t v___x_1363_; 
v_k_1358_ = lean_ctor_get(v_t_1355_, 1);
v_v_1359_ = lean_ctor_get(v_t_1355_, 2);
v_l_1360_ = lean_ctor_get(v_t_1355_, 3);
v_r_1361_ = lean_ctor_get(v_t_1355_, 4);
v___x_1362_ = lean_unbox_uint64(v_k_1358_);
v___x_1363_ = lean_uint64_dec_lt(v_k_1356_, v___x_1362_);
if (v___x_1363_ == 0)
{
uint64_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_unbox_uint64(v_k_1358_);
v___x_1365_ = lean_uint64_dec_eq(v_k_1356_, v___x_1364_);
if (v___x_1365_ == 0)
{
v_t_1355_ = v_r_1361_;
goto _start;
}
else
{
lean_inc(v_v_1359_);
return v_v_1359_;
}
}
else
{
v_t_1355_ = v_l_1360_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1357_);
return v_fallback_1357_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1355_ = stack[0].m_obj;
uint64_t v_k_1356_ = stack[1].m_num;
lean_object* v_fallback_1357_ = stack[2].m_obj;
lean_object* v_res_1368_;
v_res_1368_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1355_, v_k_1356_, v_fallback_1357_);
stack->m_obj
 = v_res_1368_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1369_, lean_object* v_k_1370_, lean_object* v_fallback_1371_){
_start:
{
uint64_t v_k_boxed_1372_; lean_object* v_res_1373_; 
v_k_boxed_1372_ = lean_unbox_uint64(v_k_1370_);
lean_dec_ref(v_k_1370_);
v_res_1373_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1369_, v_k_boxed_1372_, v_fallback_1371_);
lean_dec(v_fallback_1371_);
lean_dec(v_t_1369_);
return v_res_1373_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1374_, lean_object* v_v_1375_, lean_object* v_t_1376_){
_start:
{
if (lean_obj_tag(v_t_1376_) == 0)
{
lean_object* v_size_1377_; lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v_l_1380_; lean_object* v_r_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1665_; 
v_size_1377_ = lean_ctor_get(v_t_1376_, 0);
v_k_1378_ = lean_ctor_get(v_t_1376_, 1);
v_v_1379_ = lean_ctor_get(v_t_1376_, 2);
v_l_1380_ = lean_ctor_get(v_t_1376_, 3);
v_r_1381_ = lean_ctor_get(v_t_1376_, 4);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_t_1376_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1383_ = v_t_1376_;
v_isShared_1384_ = v_isSharedCheck_1665_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_r_1381_);
lean_inc(v_l_1380_);
lean_inc(v_v_1379_);
lean_inc(v_k_1378_);
lean_inc(v_size_1377_);
lean_dec(v_t_1376_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1665_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint64_t v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_unbox_uint64(v_k_1378_);
v___x_1386_ = lean_uint64_dec_lt(v_k_1374_, v___x_1385_);
if (v___x_1386_ == 0)
{
uint64_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = lean_unbox_uint64(v_k_1378_);
v___x_1388_ = lean_uint64_dec_eq(v_k_1374_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v_impl_1389_; lean_object* v___x_1390_; 
lean_dec(v_size_1377_);
v_impl_1389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1374_, v_v_1375_, v_r_1381_);
v___x_1390_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1380_) == 0)
{
lean_object* v_size_1391_; lean_object* v_size_1392_; lean_object* v_k_1393_; lean_object* v_v_1394_; lean_object* v_l_1395_; lean_object* v_r_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_size_1391_ = lean_ctor_get(v_l_1380_, 0);
v_size_1392_ = lean_ctor_get(v_impl_1389_, 0);
v_k_1393_ = lean_ctor_get(v_impl_1389_, 1);
v_v_1394_ = lean_ctor_get(v_impl_1389_, 2);
v_l_1395_ = lean_ctor_get(v_impl_1389_, 3);
lean_inc(v_l_1395_);
v_r_1396_ = lean_ctor_get(v_impl_1389_, 4);
v___x_1397_ = lean_unsigned_to_nat(3u);
v___x_1398_ = lean_nat_mul(v___x_1397_, v_size_1391_);
v___x_1399_ = lean_nat_dec_lt(v___x_1398_, v_size_1392_);
lean_dec(v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_dec(v_l_1395_);
v___x_1400_ = lean_nat_add(v___x_1390_, v_size_1391_);
v___x_1401_ = lean_nat_add(v___x_1400_, v_size_1392_);
lean_dec(v___x_1400_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_impl_1389_);
lean_ctor_set(v___x_1383_, 0, v___x_1401_);
v___x_1403_ = v___x_1383_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_impl_1389_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1468_; 
lean_inc(v_r_1396_);
lean_inc(v_v_1394_);
lean_inc(v_k_1393_);
lean_inc(v_size_1392_);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_impl_1389_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; 
v_unused_1469_ = lean_ctor_get(v_impl_1389_, 4);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_impl_1389_, 3);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_impl_1389_, 2);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_impl_1389_, 1);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_impl_1389_, 0);
lean_dec(v_unused_1473_);
v___x_1406_ = v_impl_1389_;
v_isShared_1407_ = v_isSharedCheck_1468_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_impl_1389_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1468_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_size_1408_; lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v_l_1411_; lean_object* v_r_1412_; lean_object* v_size_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_size_1408_ = lean_ctor_get(v_l_1395_, 0);
v_k_1409_ = lean_ctor_get(v_l_1395_, 1);
v_v_1410_ = lean_ctor_get(v_l_1395_, 2);
v_l_1411_ = lean_ctor_get(v_l_1395_, 3);
v_r_1412_ = lean_ctor_get(v_l_1395_, 4);
v_size_1413_ = lean_ctor_get(v_r_1396_, 0);
v___x_1414_ = lean_unsigned_to_nat(2u);
v___x_1415_ = lean_nat_mul(v___x_1414_, v_size_1413_);
v___x_1416_ = lean_nat_dec_lt(v_size_1408_, v___x_1415_);
lean_dec(v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_r_1412_);
lean_inc(v_l_1411_);
lean_inc(v_v_1410_);
lean_inc(v_k_1409_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_l_1395_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1445_ = lean_ctor_get(v_l_1395_, 4);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_l_1395_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_l_1395_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_l_1395_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1395_, 0);
lean_dec(v_unused_1449_);
v___x_1418_ = v_l_1395_;
v_isShared_1419_ = v_isSharedCheck_1444_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v_l_1395_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1444_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1434_; 
v___x_1420_ = lean_nat_add(v___x_1390_, v_size_1391_);
v___x_1421_ = lean_nat_add(v___x_1420_, v_size_1392_);
lean_dec(v_size_1392_);
if (lean_obj_tag(v_l_1411_) == 0)
{
lean_object* v_size_1442_; 
v_size_1442_ = lean_ctor_get(v_l_1411_, 0);
lean_inc(v_size_1442_);
v___y_1434_ = v_size_1442_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___y_1434_ = v___x_1443_;
goto v___jp_1433_;
}
v___jp_1422_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_nat_add(v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec(v___y_1424_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 4, v_r_1396_);
lean_ctor_set(v___x_1418_, 3, v_r_1412_);
lean_ctor_set(v___x_1418_, 2, v_v_1394_);
lean_ctor_set(v___x_1418_, 1, v_k_1393_);
lean_ctor_set(v___x_1418_, 0, v___x_1426_);
v___x_1428_ = v___x_1418_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1393_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1394_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_r_1412_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_r_1396_);
v___x_1428_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1430_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 4, v___x_1428_);
lean_ctor_set(v___x_1406_, 3, v___y_1423_);
lean_ctor_set(v___x_1406_, 2, v_v_1410_);
lean_ctor_set(v___x_1406_, 1, v_k_1409_);
lean_ctor_set(v___x_1406_, 0, v___x_1421_);
v___x_1430_ = v___x_1406_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1409_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1410_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v___y_1423_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
v___jp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_nat_add(v___x_1420_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec(v___x_1420_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1411_);
lean_ctor_set(v___x_1383_, 0, v___x_1435_);
v___x_1437_ = v___x_1383_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_l_1411_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_nat_add(v___x_1390_, v_size_1413_);
if (lean_obj_tag(v_r_1412_) == 0)
{
lean_object* v_size_1439_; 
v_size_1439_ = lean_ctor_get(v_r_1412_, 0);
lean_inc(v_size_1439_);
v___y_1423_ = v___x_1437_;
v___y_1424_ = v___x_1438_;
v___y_1425_ = v_size_1439_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___y_1423_ = v___x_1437_;
v___y_1424_ = v___x_1438_;
v___y_1425_ = v___x_1440_;
goto v___jp_1422_;
}
}
}
}
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
lean_del_object(v___x_1383_);
v___x_1450_ = lean_nat_add(v___x_1390_, v_size_1391_);
v___x_1451_ = lean_nat_add(v___x_1450_, v_size_1392_);
lean_dec(v_size_1392_);
v___x_1452_ = lean_nat_add(v___x_1450_, v_size_1408_);
lean_dec(v___x_1450_);
lean_inc_ref(v_l_1380_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 4, v_l_1395_);
lean_ctor_set(v___x_1406_, 3, v_l_1380_);
lean_ctor_set(v___x_1406_, 2, v_v_1379_);
lean_ctor_set(v___x_1406_, 1, v_k_1378_);
lean_ctor_set(v___x_1406_, 0, v___x_1452_);
v___x_1454_ = v___x_1406_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_l_1395_);
v___x_1454_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_isSharedCheck_1461_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; lean_object* v_unused_1463_; lean_object* v_unused_1464_; lean_object* v_unused_1465_; lean_object* v_unused_1466_; 
v_unused_1462_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1466_);
v___x_1456_ = v_l_1380_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v_l_1380_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 4, v_r_1396_);
lean_ctor_set(v___x_1456_, 3, v___x_1454_);
lean_ctor_set(v___x_1456_, 2, v_v_1394_);
lean_ctor_set(v___x_1456_, 1, v_k_1393_);
lean_ctor_set(v___x_1456_, 0, v___x_1451_);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_k_1393_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_v_1394_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_r_1396_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1474_; 
v_l_1474_ = lean_ctor_get(v_impl_1389_, 3);
lean_inc(v_l_1474_);
if (lean_obj_tag(v_l_1474_) == 0)
{
lean_object* v_r_1475_; lean_object* v_k_1476_; lean_object* v_v_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1500_; 
v_r_1475_ = lean_ctor_get(v_impl_1389_, 4);
v_k_1476_ = lean_ctor_get(v_impl_1389_, 1);
v_v_1477_ = lean_ctor_get(v_impl_1389_, 2);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_impl_1389_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1501_ = lean_ctor_get(v_impl_1389_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_impl_1389_, 0);
lean_dec(v_unused_1502_);
v___x_1479_ = v_impl_1389_;
v_isShared_1480_ = v_isSharedCheck_1500_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_r_1475_);
lean_inc(v_v_1477_);
lean_inc(v_k_1476_);
lean_dec(v_impl_1389_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1500_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_k_1481_; lean_object* v_v_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1496_; 
v_k_1481_ = lean_ctor_get(v_l_1474_, 1);
v_v_1482_ = lean_ctor_get(v_l_1474_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_l_1474_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; 
v_unused_1497_ = lean_ctor_get(v_l_1474_, 4);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_l_1474_, 3);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_l_1474_, 0);
lean_dec(v_unused_1499_);
v___x_1484_ = v_l_1474_;
v_isShared_1485_ = v_isSharedCheck_1496_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_v_1482_);
lean_inc(v_k_1481_);
lean_dec(v_l_1474_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1496_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1475_, 2);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_r_1475_);
lean_ctor_set(v___x_1484_, 3, v_r_1475_);
lean_ctor_set(v___x_1484_, 2, v_v_1379_);
lean_ctor_set(v___x_1484_, 1, v_k_1378_);
lean_ctor_set(v___x_1484_, 0, v___x_1390_);
v___x_1488_ = v___x_1484_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_r_1475_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_r_1475_);
v___x_1488_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
lean_inc(v_r_1475_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 3, v_r_1475_);
lean_ctor_set(v___x_1479_, 0, v___x_1390_);
v___x_1490_ = v___x_1479_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_r_1475_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_r_1475_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1490_);
lean_ctor_set(v___x_1383_, 3, v___x_1488_);
lean_ctor_set(v___x_1383_, 2, v_v_1482_);
lean_ctor_set(v___x_1383_, 1, v_k_1481_);
lean_ctor_set(v___x_1383_, 0, v___x_1486_);
v___x_1492_ = v___x_1383_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
else
{
lean_object* v_r_1503_; 
v_r_1503_ = lean_ctor_get(v_impl_1389_, 4);
lean_inc(v_r_1503_);
if (lean_obj_tag(v_r_1503_) == 0)
{
lean_object* v_k_1504_; lean_object* v_v_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1516_; 
v_k_1504_ = lean_ctor_get(v_impl_1389_, 1);
v_v_1505_ = lean_ctor_get(v_impl_1389_, 2);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_impl_1389_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1517_ = lean_ctor_get(v_impl_1389_, 4);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_impl_1389_, 3);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_impl_1389_, 0);
lean_dec(v_unused_1519_);
v___x_1507_ = v_impl_1389_;
v_isShared_1508_ = v_isSharedCheck_1516_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_v_1505_);
lean_inc(v_k_1504_);
lean_dec(v_impl_1389_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1516_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(3u);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v_l_1474_);
lean_ctor_set(v___x_1507_, 2, v_v_1379_);
lean_ctor_set(v___x_1507_, 1, v_k_1378_);
lean_ctor_set(v___x_1507_, 0, v___x_1390_);
v___x_1511_ = v___x_1507_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_l_1474_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_l_1474_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1503_);
lean_ctor_set(v___x_1383_, 3, v___x_1511_);
lean_ctor_set(v___x_1383_, 2, v_v_1505_);
lean_ctor_set(v___x_1383_, 1, v_k_1504_);
lean_ctor_set(v___x_1383_, 0, v___x_1509_);
v___x_1513_ = v___x_1383_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1504_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1505_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1503_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_unsigned_to_nat(2u);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_impl_1389_);
lean_ctor_set(v___x_1383_, 3, v_r_1503_);
lean_ctor_set(v___x_1383_, 0, v___x_1520_);
v___x_1522_ = v___x_1383_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_r_1503_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_impl_1389_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_dec(v_v_1379_);
lean_dec(v_k_1378_);
v___x_1524_ = lean_box_uint64(v_k_1374_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 2, v_v_1375_);
lean_ctor_set(v___x_1383_, 1, v___x_1524_);
v___x_1526_ = v___x_1383_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_size_1377_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v_r_1381_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
else
{
lean_object* v_impl_1528_; lean_object* v___x_1529_; 
lean_dec(v_size_1377_);
v_impl_1528_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1374_, v_v_1375_, v_l_1380_);
v___x_1529_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1381_) == 0)
{
lean_object* v_size_1530_; lean_object* v_size_1531_; lean_object* v_k_1532_; lean_object* v_v_1533_; lean_object* v_l_1534_; lean_object* v_r_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_size_1530_ = lean_ctor_get(v_r_1381_, 0);
v_size_1531_ = lean_ctor_get(v_impl_1528_, 0);
v_k_1532_ = lean_ctor_get(v_impl_1528_, 1);
v_v_1533_ = lean_ctor_get(v_impl_1528_, 2);
v_l_1534_ = lean_ctor_get(v_impl_1528_, 3);
v_r_1535_ = lean_ctor_get(v_impl_1528_, 4);
lean_inc(v_r_1535_);
v___x_1536_ = lean_unsigned_to_nat(3u);
v___x_1537_ = lean_nat_mul(v___x_1536_, v_size_1530_);
v___x_1538_ = lean_nat_dec_lt(v___x_1537_, v_size_1531_);
lean_dec(v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_dec(v_r_1535_);
v___x_1539_ = lean_nat_add(v___x_1529_, v_size_1531_);
v___x_1540_ = lean_nat_add(v___x_1539_, v_size_1530_);
lean_dec(v___x_1539_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 3, v_impl_1528_);
lean_ctor_set(v___x_1383_, 0, v___x_1540_);
v___x_1542_ = v___x_1383_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_impl_1528_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_r_1381_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1609_; 
lean_inc(v_l_1534_);
lean_inc(v_v_1533_);
lean_inc(v_k_1532_);
lean_inc(v_size_1531_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_impl_1528_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1610_ = lean_ctor_get(v_impl_1528_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_impl_1528_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_impl_1528_, 2);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_impl_1528_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_impl_1528_, 0);
lean_dec(v_unused_1614_);
v___x_1545_ = v_impl_1528_;
v_isShared_1546_ = v_isSharedCheck_1609_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v_impl_1528_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1609_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_size_1547_; lean_object* v_size_1548_; lean_object* v_k_1549_; lean_object* v_v_1550_; lean_object* v_l_1551_; lean_object* v_r_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_size_1547_ = lean_ctor_get(v_l_1534_, 0);
v_size_1548_ = lean_ctor_get(v_r_1535_, 0);
v_k_1549_ = lean_ctor_get(v_r_1535_, 1);
v_v_1550_ = lean_ctor_get(v_r_1535_, 2);
v_l_1551_ = lean_ctor_get(v_r_1535_, 3);
v_r_1552_ = lean_ctor_get(v_r_1535_, 4);
v___x_1553_ = lean_unsigned_to_nat(2u);
v___x_1554_ = lean_nat_mul(v___x_1553_, v_size_1547_);
v___x_1555_ = lean_nat_dec_lt(v_size_1548_, v___x_1554_);
lean_dec(v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1584_; 
lean_inc(v_r_1552_);
lean_inc(v_l_1551_);
lean_inc(v_v_1550_);
lean_inc(v_k_1549_);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_r_1535_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1585_ = lean_ctor_get(v_r_1535_, 4);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_r_1535_, 3);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_r_1535_, 2);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_r_1535_, 1);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_r_1535_, 0);
lean_dec(v_unused_1589_);
v___x_1557_ = v_r_1535_;
v_isShared_1558_ = v_isSharedCheck_1584_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v_r_1535_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1584_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___x_1572_; lean_object* v___y_1574_; 
v___x_1559_ = lean_nat_add(v___x_1529_, v_size_1531_);
lean_dec(v_size_1531_);
v___x_1560_ = lean_nat_add(v___x_1559_, v_size_1530_);
lean_dec(v___x_1559_);
v___x_1572_ = lean_nat_add(v___x_1529_, v_size_1547_);
if (lean_obj_tag(v_l_1551_) == 0)
{
lean_object* v_size_1582_; 
v_size_1582_ = lean_ctor_get(v_l_1551_, 0);
lean_inc(v_size_1582_);
v___y_1574_ = v_size_1582_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_unsigned_to_nat(0u);
v___y_1574_ = v___x_1583_;
goto v___jp_1573_;
}
v___jp_1561_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_nat_add(v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec(v___y_1563_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v_r_1381_);
lean_ctor_set(v___x_1557_, 3, v_r_1552_);
lean_ctor_set(v___x_1557_, 2, v_v_1379_);
lean_ctor_set(v___x_1557_, 1, v_k_1378_);
lean_ctor_set(v___x_1557_, 0, v___x_1565_);
v___x_1567_ = v___x_1557_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_r_1552_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_r_1381_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v___x_1567_);
lean_ctor_set(v___x_1545_, 3, v___y_1562_);
lean_ctor_set(v___x_1545_, 2, v_v_1550_);
lean_ctor_set(v___x_1545_, 1, v_k_1549_);
lean_ctor_set(v___x_1545_, 0, v___x_1560_);
v___x_1569_ = v___x_1545_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1549_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1550_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v___y_1562_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
v___jp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = lean_nat_add(v___x_1572_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec(v___x_1572_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1551_);
lean_ctor_set(v___x_1383_, 3, v_l_1534_);
lean_ctor_set(v___x_1383_, 2, v_v_1533_);
lean_ctor_set(v___x_1383_, 1, v_k_1532_);
lean_ctor_set(v___x_1383_, 0, v___x_1575_);
v___x_1577_ = v___x_1383_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1532_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1533_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_l_1534_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_l_1551_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_nat_add(v___x_1529_, v_size_1530_);
if (lean_obj_tag(v_r_1552_) == 0)
{
lean_object* v_size_1579_; 
v_size_1579_ = lean_ctor_get(v_r_1552_, 0);
lean_inc(v_size_1579_);
v___y_1562_ = v___x_1577_;
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_size_1579_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
v___y_1562_ = v___x_1577_;
v___y_1563_ = v___x_1578_;
v___y_1564_ = v___x_1580_;
goto v___jp_1561_;
}
}
}
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_del_object(v___x_1383_);
v___x_1590_ = lean_nat_add(v___x_1529_, v_size_1531_);
lean_dec(v_size_1531_);
v___x_1591_ = lean_nat_add(v___x_1590_, v_size_1530_);
lean_dec(v___x_1590_);
v___x_1592_ = lean_nat_add(v___x_1529_, v_size_1530_);
v___x_1593_ = lean_nat_add(v___x_1592_, v_size_1548_);
lean_dec(v___x_1592_);
lean_inc_ref(v_r_1381_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v_r_1381_);
lean_ctor_set(v___x_1545_, 3, v_r_1535_);
lean_ctor_set(v___x_1545_, 2, v_v_1379_);
lean_ctor_set(v___x_1545_, 1, v_k_1378_);
lean_ctor_set(v___x_1545_, 0, v___x_1593_);
v___x_1595_ = v___x_1545_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_r_1535_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_r_1381_);
v___x_1595_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1603_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_r_1381_, 2);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_r_1381_, 1);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1607_);
v___x_1597_ = v_r_1381_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v_r_1381_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 4, v___x_1595_);
lean_ctor_set(v___x_1597_, 3, v_l_1534_);
lean_ctor_set(v___x_1597_, 2, v_v_1533_);
lean_ctor_set(v___x_1597_, 1, v_k_1532_);
lean_ctor_set(v___x_1597_, 0, v___x_1591_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1532_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1533_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1534_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v___x_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1615_; 
v_l_1615_ = lean_ctor_get(v_impl_1528_, 3);
if (lean_obj_tag(v_l_1615_) == 0)
{
lean_object* v_r_1616_; lean_object* v_k_1617_; lean_object* v_v_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1629_; 
lean_inc_ref(v_l_1615_);
v_r_1616_ = lean_ctor_get(v_impl_1528_, 4);
v_k_1617_ = lean_ctor_get(v_impl_1528_, 1);
v_v_1618_ = lean_ctor_get(v_impl_1528_, 2);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_impl_1528_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; lean_object* v_unused_1631_; 
v_unused_1630_ = lean_ctor_get(v_impl_1528_, 3);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_impl_1528_, 0);
lean_dec(v_unused_1631_);
v___x_1620_ = v_impl_1528_;
v_isShared_1621_ = v_isSharedCheck_1629_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_r_1616_);
lean_inc(v_v_1618_);
lean_inc(v_k_1617_);
lean_dec(v_impl_1528_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1629_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1616_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 3, v_r_1616_);
lean_ctor_set(v___x_1620_, 2, v_v_1379_);
lean_ctor_set(v___x_1620_, 1, v_k_1378_);
lean_ctor_set(v___x_1620_, 0, v___x_1529_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_r_1616_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_r_1616_);
v___x_1624_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1624_);
lean_ctor_set(v___x_1383_, 3, v_l_1615_);
lean_ctor_set(v___x_1383_, 2, v_v_1618_);
lean_ctor_set(v___x_1383_, 1, v_k_1617_);
lean_ctor_set(v___x_1383_, 0, v___x_1622_);
v___x_1626_ = v___x_1383_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_k_1617_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_v_1618_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_l_1615_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_r_1632_; 
v_r_1632_ = lean_ctor_get(v_impl_1528_, 4);
lean_inc(v_r_1632_);
if (lean_obj_tag(v_r_1632_) == 0)
{
lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1657_; 
lean_inc(v_l_1615_);
v_k_1633_ = lean_ctor_get(v_impl_1528_, 1);
v_v_1634_ = lean_ctor_get(v_impl_1528_, 2);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_impl_1528_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; lean_object* v_unused_1659_; lean_object* v_unused_1660_; 
v_unused_1658_ = lean_ctor_get(v_impl_1528_, 4);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_impl_1528_, 3);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_impl_1528_, 0);
lean_dec(v_unused_1660_);
v___x_1636_ = v_impl_1528_;
v_isShared_1637_ = v_isSharedCheck_1657_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_v_1634_);
lean_inc(v_k_1633_);
lean_dec(v_impl_1528_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1657_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_k_1638_; lean_object* v_v_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1653_; 
v_k_1638_ = lean_ctor_get(v_r_1632_, 1);
v_v_1639_ = lean_ctor_get(v_r_1632_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_r_1632_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; 
v_unused_1654_ = lean_ctor_get(v_r_1632_, 4);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_r_1632_, 3);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_r_1632_, 0);
lean_dec(v_unused_1656_);
v___x_1641_ = v_r_1632_;
v_isShared_1642_ = v_isSharedCheck_1653_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_v_1639_);
lean_inc(v_k_1638_);
lean_dec(v_r_1632_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1653_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_unsigned_to_nat(3u);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 4, v_l_1615_);
lean_ctor_set(v___x_1641_, 3, v_l_1615_);
lean_ctor_set(v___x_1641_, 2, v_v_1634_);
lean_ctor_set(v___x_1641_, 1, v_k_1633_);
lean_ctor_set(v___x_1641_, 0, v___x_1529_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1633_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1634_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_l_1615_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_l_1615_);
v___x_1645_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1647_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 4, v_l_1615_);
lean_ctor_set(v___x_1636_, 2, v_v_1379_);
lean_ctor_set(v___x_1636_, 1, v_k_1378_);
lean_ctor_set(v___x_1636_, 0, v___x_1529_);
v___x_1647_ = v___x_1636_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_l_1615_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_l_1615_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1647_);
lean_ctor_set(v___x_1383_, 3, v___x_1645_);
lean_ctor_set(v___x_1383_, 2, v_v_1639_);
lean_ctor_set(v___x_1383_, 1, v_k_1638_);
lean_ctor_set(v___x_1383_, 0, v___x_1643_);
v___x_1649_ = v___x_1383_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1638_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1639_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_unsigned_to_nat(2u);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1632_);
lean_ctor_set(v___x_1383_, 3, v_impl_1528_);
lean_ctor_set(v___x_1383_, 0, v___x_1661_);
v___x_1663_ = v___x_1383_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_impl_1528_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_r_1632_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_box_uint64(v_k_1374_);
v___x_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
lean_ctor_set(v___x_1668_, 2, v_v_1375_);
lean_ctor_set(v___x_1668_, 3, v_t_1376_);
lean_ctor_set(v___x_1668_, 4, v_t_1376_);
return v___x_1668_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_1374_ = stack[0].m_num;
lean_object* v_v_1375_ = stack[1].m_obj;
lean_object* v_t_1376_ = stack[2].m_obj;
lean_object* v_res_1669_;
v_res_1669_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1374_, v_v_1375_, v_t_1376_);
stack->m_obj
 = v_res_1669_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1670_, lean_object* v_v_1671_, lean_object* v_t_1672_){
_start:
{
uint64_t v_k_boxed_1673_; lean_object* v_res_1674_; 
v_k_boxed_1673_ = lean_unbox_uint64(v_k_1670_);
lean_dec_ref(v_k_1670_);
v_res_1674_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1673_, v_v_1671_, v_t_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1675_, lean_object* v_s_1676_){
_start:
{
uint64_t v_javascriptHash_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_javascriptHash_1677_ = lean_ctor_get_uint64(v_wi_1675_, sizeof(void*)*2);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_wi_1675_);
v___x_1679_ = lean_box(0);
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1676_, v_javascriptHash_1677_, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1678_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1677_, v___x_1681_, v_s_1676_);
return v___x_1682_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v_env_1689_; lean_object* v_nextMacroScope_1690_; lean_object* v_ngen_1691_; lean_object* v_auxDeclNGen_1692_; lean_object* v_traceState_1693_; lean_object* v_recordedDeps_1694_; lean_object* v_messages_1695_; lean_object* v_infoState_1696_; lean_object* v_snapshotTasks_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1725_; 
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1687_, 0, v_wi_1683_);
v___x_1688_ = lean_st_ref_take(v___y_1685_);
v_env_1689_ = lean_ctor_get(v___x_1688_, 0);
v_nextMacroScope_1690_ = lean_ctor_get(v___x_1688_, 1);
v_ngen_1691_ = lean_ctor_get(v___x_1688_, 2);
v_auxDeclNGen_1692_ = lean_ctor_get(v___x_1688_, 3);
v_traceState_1693_ = lean_ctor_get(v___x_1688_, 4);
v_recordedDeps_1694_ = lean_ctor_get(v___x_1688_, 6);
v_messages_1695_ = lean_ctor_get(v___x_1688_, 7);
v_infoState_1696_ = lean_ctor_get(v___x_1688_, 8);
v_snapshotTasks_1697_ = lean_ctor_get(v___x_1688_, 9);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1688_, 5);
lean_dec(v_unused_1726_);
v___x_1699_ = v___x_1688_;
v_isShared_1700_ = v_isSharedCheck_1725_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snapshotTasks_1697_);
lean_inc(v_infoState_1696_);
lean_inc(v_messages_1695_);
lean_inc(v_recordedDeps_1694_);
lean_inc(v_traceState_1693_);
lean_inc(v_auxDeclNGen_1692_);
lean_inc(v_ngen_1691_);
lean_inc(v_nextMacroScope_1690_);
lean_inc(v_env_1689_);
lean_dec(v___x_1688_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1725_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1701_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1702_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1701_, v_env_1689_, v___f_1687_);
v___x_1703_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 5, v___x_1703_);
lean_ctor_set(v___x_1699_, 0, v___x_1702_);
v___x_1705_ = v___x_1699_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_nextMacroScope_1690_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_ngen_1691_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_auxDeclNGen_1692_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_traceState_1693_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_recordedDeps_1694_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_messages_1695_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_infoState_1696_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_snapshotTasks_1697_);
v___x_1705_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v_mctx_1708_; lean_object* v_zetaDeltaFVarIds_1709_; lean_object* v_postponed_1710_; lean_object* v_diag_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1722_; 
v___x_1706_ = lean_st_ref_put(v___y_1685_, v___x_1705_);
v___x_1707_ = lean_st_ref_take(v___y_1684_);
v_mctx_1708_ = lean_ctor_get(v___x_1707_, 0);
v_zetaDeltaFVarIds_1709_ = lean_ctor_get(v___x_1707_, 2);
v_postponed_1710_ = lean_ctor_get(v___x_1707_, 3);
v_diag_1711_ = lean_ctor_get(v___x_1707_, 4);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v___x_1707_, 1);
lean_dec(v_unused_1723_);
v___x_1713_ = v___x_1707_;
v_isShared_1714_ = v_isSharedCheck_1722_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_diag_1711_);
lean_inc(v_postponed_1710_);
lean_inc(v_zetaDeltaFVarIds_1709_);
lean_inc(v_mctx_1708_);
lean_dec(v___x_1707_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1722_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1716_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_mctx_1708_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_zetaDeltaFVarIds_1709_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_postponed_1710_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_diag_1711_);
v___x_1718_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_st_ref_put(v___y_1684_, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1715_);
return v___x_1720_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_wi_1683_ = stack[0].m_obj;
lean_object* v___y_1684_ = stack[1].m_obj;
lean_object* v___y_1685_ = stack[2].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1683_, v___y_1684_, v___y_1685_);
stack->m_obj
 = v_res_1727_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec(v___y_1729_);
return v_res_1732_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(lean_object* v_ext_1733_, lean_object* v_b_1734_, uint8_t v_kind_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_toCold_1740_; lean_object* v_currNamespace_1741_; lean_object* v___x_1742_; lean_object* v_env_1743_; lean_object* v_nextMacroScope_1744_; lean_object* v_ngen_1745_; lean_object* v_auxDeclNGen_1746_; lean_object* v_traceState_1747_; lean_object* v_recordedDeps_1748_; lean_object* v_messages_1749_; lean_object* v_infoState_1750_; lean_object* v_snapshotTasks_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1778_; 
v_toCold_1740_ = lean_ctor_get(v___y_1737_, 0);
v_currNamespace_1741_ = lean_ctor_get(v_toCold_1740_, 4);
v___x_1742_ = lean_st_ref_take(v___y_1738_);
v_env_1743_ = lean_ctor_get(v___x_1742_, 0);
v_nextMacroScope_1744_ = lean_ctor_get(v___x_1742_, 1);
v_ngen_1745_ = lean_ctor_get(v___x_1742_, 2);
v_auxDeclNGen_1746_ = lean_ctor_get(v___x_1742_, 3);
v_traceState_1747_ = lean_ctor_get(v___x_1742_, 4);
v_recordedDeps_1748_ = lean_ctor_get(v___x_1742_, 6);
v_messages_1749_ = lean_ctor_get(v___x_1742_, 7);
v_infoState_1750_ = lean_ctor_get(v___x_1742_, 8);
v_snapshotTasks_1751_ = lean_ctor_get(v___x_1742_, 9);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1742_, 5);
lean_dec(v_unused_1779_);
v___x_1753_ = v___x_1742_;
v_isShared_1754_ = v_isSharedCheck_1778_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_snapshotTasks_1751_);
lean_inc(v_infoState_1750_);
lean_inc(v_messages_1749_);
lean_inc(v_recordedDeps_1748_);
lean_inc(v_traceState_1747_);
lean_inc(v_auxDeclNGen_1746_);
lean_inc(v_ngen_1745_);
lean_inc(v_nextMacroScope_1744_);
lean_inc(v_env_1743_);
lean_dec(v___x_1742_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1778_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_inc(v_currNamespace_1741_);
v___x_1755_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1743_, v_ext_1733_, v_b_1734_, v_kind_1735_, v_currNamespace_1741_);
v___x_1756_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 5, v___x_1756_);
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_nextMacroScope_1744_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_ngen_1745_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_auxDeclNGen_1746_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_traceState_1747_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1777_, 6, v_recordedDeps_1748_);
lean_ctor_set(v_reuseFailAlloc_1777_, 7, v_messages_1749_);
lean_ctor_set(v_reuseFailAlloc_1777_, 8, v_infoState_1750_);
lean_ctor_set(v_reuseFailAlloc_1777_, 9, v_snapshotTasks_1751_);
v___x_1758_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_mctx_1761_; lean_object* v_zetaDeltaFVarIds_1762_; lean_object* v_postponed_1763_; lean_object* v_diag_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1775_; 
v___x_1759_ = lean_st_ref_put(v___y_1738_, v___x_1758_);
v___x_1760_ = lean_st_ref_take(v___y_1736_);
v_mctx_1761_ = lean_ctor_get(v___x_1760_, 0);
v_zetaDeltaFVarIds_1762_ = lean_ctor_get(v___x_1760_, 2);
v_postponed_1763_ = lean_ctor_get(v___x_1760_, 3);
v_diag_1764_ = lean_ctor_get(v___x_1760_, 4);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1760_, 1);
lean_dec(v_unused_1776_);
v___x_1766_ = v___x_1760_;
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_diag_1764_);
lean_inc(v_postponed_1763_);
lean_inc(v_zetaDeltaFVarIds_1762_);
lean_inc(v_mctx_1761_);
lean_dec(v___x_1760_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1769_);
v___x_1771_ = v___x_1766_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_mctx_1761_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_zetaDeltaFVarIds_1762_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_postponed_1763_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v_diag_1764_);
v___x_1771_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_st_ref_put(v___y_1736_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1768_);
return v___x_1773_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1733_ = stack[0].m_obj;
lean_object* v_b_1734_ = stack[1].m_obj;
uint8_t v_kind_1735_ = stack[2].m_num;
lean_object* v___y_1736_ = stack[3].m_obj;
lean_object* v___y_1737_ = stack[4].m_obj;
lean_object* v___y_1738_ = stack[5].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_1733_, v_b_1734_, v_kind_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(lean_object* v_ext_1781_, lean_object* v_b_1782_, lean_object* v_kind_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
uint8_t v_kind_boxed_1788_; lean_object* v_res_1789_; 
v_kind_boxed_1788_ = lean_unbox(v_kind_1783_);
v_res_1789_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_1781_, v_b_1782_, v_kind_boxed_1788_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1789_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1790_, lean_object* v_n_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1799_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1800_ = lean_box_uint64(v_h_1790_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_n_1791_);
v___x_1802_ = 2;
v___x_1803_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1799_, v___x_1801_, v___x_1802_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1803_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_1790_ = stack[0].m_num;
lean_object* v_n_1791_ = stack[1].m_obj;
lean_object* v___y_1792_ = stack[2].m_obj;
lean_object* v___y_1793_ = stack[3].m_obj;
lean_object* v___y_1794_ = stack[4].m_obj;
lean_object* v___y_1795_ = stack[5].m_obj;
lean_object* v___y_1796_ = stack[6].m_obj;
lean_object* v___y_1797_ = stack[7].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_1790_, v_n_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1805_, lean_object* v_n_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint64_t v_h_boxed_1814_; lean_object* v_res_1815_; 
v_h_boxed_1814_ = lean_unbox_uint64(v_h_1805_);
lean_dec_ref(v_h_1805_);
v_res_1815_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1814_, v_n_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1815_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1816_, lean_object* v_n_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1825_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1826_ = lean_box_uint64(v_h_1816_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_n_1817_);
v___x_1828_ = 0;
v___x_1829_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1825_, v___x_1827_, v___x_1828_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1829_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_1816_ = stack[0].m_num;
lean_object* v_n_1817_ = stack[1].m_obj;
lean_object* v___y_1818_ = stack[2].m_obj;
lean_object* v___y_1819_ = stack[3].m_obj;
lean_object* v___y_1820_ = stack[4].m_obj;
lean_object* v___y_1821_ = stack[5].m_obj;
lean_object* v___y_1822_ = stack[6].m_obj;
lean_object* v___y_1823_ = stack[7].m_obj;
lean_object* v_res_1830_;
v_res_1830_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_1816_, v_n_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
stack->m_obj
 = v_res_1830_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1831_, lean_object* v_n_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint64_t v_h_boxed_1840_; lean_object* v_res_1841_; 
v_h_boxed_1840_ = lean_unbox_uint64(v_h_1831_);
lean_dec_ref(v_h_1831_);
v_res_1841_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1840_, v_n_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_1842_, lean_object* v___y_1843_){
_start:
{
if (lean_obj_tag(v_x_1842_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v_x_1842_, 0);
lean_inc(v_a_1844_);
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1844_);
lean_ctor_set(v___x_1845_, 1, v___y_1843_);
return v___x_1845_;
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v_x_1842_, 0);
lean_inc(v_a_1846_);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1846_);
lean_ctor_set(v___x_1847_, 1, v___y_1843_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_1848_, v___y_1849_);
lean_dec_ref(v_x_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1851_, lean_object* v_stx_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1851_, v_stx_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
if (lean_obj_tag(v_a_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_a_1857_ = lean_ctor_get(v___x_1855_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1855_, 0);
lean_dec(v_unused_1866_);
v___x_1859_ = v___x_1855_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_box(0);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_a_1857_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
lean_object* v_val_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1895_; 
v_val_1867_ = lean_ctor_get(v_a_1856_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_a_1856_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1869_ = v_a_1856_;
v_isShared_1870_ = v_isSharedCheck_1895_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_val_1867_);
lean_dec(v_a_1856_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1895_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_snd_1871_; 
v_snd_1871_ = lean_ctor_get(v_val_1867_, 1);
lean_inc(v_snd_1871_);
lean_dec(v_val_1867_);
if (lean_obj_tag(v_snd_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1869_);
v_a_1872_ = lean_ctor_get(v___x_1855_, 1);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1855_, 2);
v_a_1873_ = lean_ctor_get(v_snd_1871_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_snd_1871_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1875_ = v_snd_1871_;
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v_snd_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1878_, v_a_1872_);
lean_dec_ref(v___x_1878_);
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1894_; 
v_a_1882_ = lean_ctor_get(v___x_1855_, 1);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1855_, 2);
v_a_1883_ = lean_ctor_get(v_snd_1871_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_snd_1871_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1885_ = v_snd_1871_;
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v_snd_1871_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v_a_1883_);
v___x_1888_ = v___x_1869_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1890_, v_a_1882_);
lean_dec_ref(v___x_1890_);
return v___x_1891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1896_ = lean_ctor_get(v___x_1855_, 0);
v_a_1897_ = lean_ctor_get(v___x_1855_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1855_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_inc(v_a_1896_);
lean_dec(v___x_1855_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1905_, lean_object* v_stx_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1905_, v_stx_1906_, v___y_1907_, v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1909_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(lean_object* v_msgData_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v_env_1917_; uint8_t v___x_1918_; lean_object* v_env_1919_; lean_object* v___x_1920_; lean_object* v_toCold_1921_; lean_object* v_mctx_1922_; lean_object* v_lctx_1923_; lean_object* v_options_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1916_ = lean_st_ref_get(v___y_1914_);
v_env_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_env_1917_);
lean_dec(v___x_1916_);
v___x_1918_ = 0;
v_env_1919_ = l_Lean_Environment_setRecordingDeps(v_env_1917_, v___x_1918_);
v___x_1920_ = lean_st_ref_get(v___y_1912_);
v_toCold_1921_ = lean_ctor_get(v___y_1913_, 0);
v_mctx_1922_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_ref(v_mctx_1922_);
lean_dec(v___x_1920_);
v_lctx_1923_ = lean_ctor_get(v___y_1911_, 2);
v_options_1924_ = lean_ctor_get(v_toCold_1921_, 2);
lean_inc_ref(v_options_1924_);
lean_inc_ref(v_lctx_1923_);
v___x_1925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1925_, 0, v_env_1919_);
lean_ctor_set(v___x_1925_, 1, v_mctx_1922_);
lean_ctor_set(v___x_1925_, 2, v_lctx_1923_);
lean_ctor_set(v___x_1925_, 3, v_options_1924_);
v___x_1926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v_msgData_1910_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1910_ = stack[0].m_obj;
lean_object* v___y_1911_ = stack[1].m_obj;
lean_object* v___y_1912_ = stack[2].m_obj;
lean_object* v___y_1913_ = stack[3].m_obj;
lean_object* v___y_1914_ = stack[4].m_obj;
lean_object* v_res_1928_;
v_res_1928_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
stack->m_obj
 = v_res_1928_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object* v_msgData_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1935_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1936_; double v___x_1937_; 
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_float_of_nat(v___x_1936_);
return v___x_1937_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1940_, lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_ref_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1994_; 
v_ref_1947_ = lean_ctor_get(v___y_1944_, 2);
v___x_1948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1994_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1994_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v_traceState_1954_; lean_object* v_env_1955_; lean_object* v_nextMacroScope_1956_; lean_object* v_ngen_1957_; lean_object* v_auxDeclNGen_1958_; lean_object* v_cache_1959_; lean_object* v_recordedDeps_1960_; lean_object* v_messages_1961_; lean_object* v_infoState_1962_; lean_object* v_snapshotTasks_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1993_; 
v___x_1953_ = lean_st_ref_take(v___y_1945_);
v_traceState_1954_ = lean_ctor_get(v___x_1953_, 4);
v_env_1955_ = lean_ctor_get(v___x_1953_, 0);
v_nextMacroScope_1956_ = lean_ctor_get(v___x_1953_, 1);
v_ngen_1957_ = lean_ctor_get(v___x_1953_, 2);
v_auxDeclNGen_1958_ = lean_ctor_get(v___x_1953_, 3);
v_cache_1959_ = lean_ctor_get(v___x_1953_, 5);
v_recordedDeps_1960_ = lean_ctor_get(v___x_1953_, 6);
v_messages_1961_ = lean_ctor_get(v___x_1953_, 7);
v_infoState_1962_ = lean_ctor_get(v___x_1953_, 8);
v_snapshotTasks_1963_ = lean_ctor_get(v___x_1953_, 9);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1965_ = v___x_1953_;
v_isShared_1966_ = v_isSharedCheck_1993_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_snapshotTasks_1963_);
lean_inc(v_infoState_1962_);
lean_inc(v_messages_1961_);
lean_inc(v_recordedDeps_1960_);
lean_inc(v_cache_1959_);
lean_inc(v_traceState_1954_);
lean_inc(v_auxDeclNGen_1958_);
lean_inc(v_ngen_1957_);
lean_inc(v_nextMacroScope_1956_);
lean_inc(v_env_1955_);
lean_dec(v___x_1953_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1993_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
uint64_t v_tid_1967_; lean_object* v_traces_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1992_; 
v_tid_1967_ = lean_ctor_get_uint64(v_traceState_1954_, sizeof(void*)*1);
v_traces_1968_ = lean_ctor_get(v_traceState_1954_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_traceState_1954_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1970_ = v_traceState_1954_;
v_isShared_1971_ = v_isSharedCheck_1992_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_traces_1968_);
lean_dec(v_traceState_1954_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1992_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; double v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1975_ = 0;
v___x_1976_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1977_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1977_, 0, v_cls_1940_);
lean_ctor_set(v___x_1977_, 1, v___x_1973_);
lean_ctor_set(v___x_1977_, 2, v___x_1976_);
lean_ctor_set_float(v___x_1977_, sizeof(void*)*3, v___x_1974_);
lean_ctor_set_float(v___x_1977_, sizeof(void*)*3 + 8, v___x_1974_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3 + 16, v___x_1975_);
v___x_1978_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1979_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v_a_1949_);
lean_ctor_set(v___x_1979_, 2, v___x_1978_);
lean_inc(v_ref_1947_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_ref_1947_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_PersistentArray_push___redArg(v_traces_1968_, v___x_1980_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1981_);
v___x_1983_ = v___x_1970_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1981_);
lean_ctor_set_uint64(v_reuseFailAlloc_1991_, sizeof(void*)*1, v_tid_1967_);
v___x_1983_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 4, v___x_1983_);
v___x_1985_ = v___x_1965_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_env_1955_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_nextMacroScope_1956_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_ngen_1957_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_auxDeclNGen_1958_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v_cache_1959_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_recordedDeps_1960_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_messages_1961_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_infoState_1962_);
lean_ctor_set(v_reuseFailAlloc_1990_, 9, v_snapshotTasks_1963_);
v___x_1985_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_st_ref_put(v___y_1945_, v___x_1985_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1972_);
v___x_1988_ = v___x_1951_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1972_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1940_ = stack[0].m_obj;
lean_object* v_msg_1941_ = stack[1].m_obj;
lean_object* v___y_1942_ = stack[2].m_obj;
lean_object* v___y_1943_ = stack[3].m_obj;
lean_object* v___y_1944_ = stack[4].m_obj;
lean_object* v___y_1945_ = stack[5].m_obj;
lean_object* v_res_1995_;
v_res_1995_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1940_, v_msg_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
stack->m_obj
 = v_res_1995_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1996_, lean_object* v_msg_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1996_, v_msg_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
if (lean_obj_tag(v_as_2007_) == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
else
{
lean_object* v_toCold_2017_; lean_object* v_options_2018_; uint8_t v_hasTrace_2019_; 
v_toCold_2017_ = lean_ctor_get(v___y_2012_, 0);
v_options_2018_ = lean_ctor_get(v_toCold_2017_, 2);
v_hasTrace_2019_ = lean_ctor_get_uint8(v_options_2018_, sizeof(void*)*1);
if (v_hasTrace_2019_ == 0)
{
lean_object* v_tail_2020_; 
v_tail_2020_ = lean_ctor_get(v_as_2007_, 1);
lean_inc(v_tail_2020_);
lean_dec_ref_known(v_as_2007_, 2);
v_as_2007_ = v_tail_2020_;
goto _start;
}
else
{
lean_object* v_head_2022_; lean_object* v_tail_2023_; lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v_inheritedTraceOptions_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_head_2022_ = lean_ctor_get(v_as_2007_, 0);
lean_inc(v_head_2022_);
v_tail_2023_ = lean_ctor_get(v_as_2007_, 1);
lean_inc(v_tail_2023_);
lean_dec_ref_known(v_as_2007_, 2);
v_fst_2024_ = lean_ctor_get(v_head_2022_, 0);
lean_inc_n(v_fst_2024_, 2);
v_snd_2025_ = lean_ctor_get(v_head_2022_, 1);
lean_inc(v_snd_2025_);
lean_dec(v_head_2022_);
v_inheritedTraceOptions_2026_ = lean_ctor_get(v_toCold_2017_, 11);
v___x_2027_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2028_ = l_Lean_Name_append(v___x_2027_, v_fst_2024_);
v___x_2029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2026_, v_options_2018_, v___x_2028_);
lean_dec(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_dec(v_snd_2025_);
lean_dec(v_fst_2024_);
v_as_2007_ = v_tail_2023_;
goto _start;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_snd_2025_);
v___x_2032_ = l_Lean_MessageData_ofFormat(v___x_2031_);
v___x_2033_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_2024_, v___x_2032_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_dec_ref_known(v___x_2033_, 1);
v_as_2007_ = v_tail_2023_;
goto _start;
}
else
{
lean_dec(v_tail_2023_);
return v___x_2033_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2007_ = stack[0].m_obj;
lean_object* v___y_2008_ = stack[1].m_obj;
lean_object* v___y_2009_ = stack[2].m_obj;
lean_object* v___y_2010_ = stack[3].m_obj;
lean_object* v___y_2011_ = stack[4].m_obj;
lean_object* v___y_2012_ = stack[5].m_obj;
lean_object* v___y_2013_ = stack[6].m_obj;
lean_object* v_res_2035_;
v_res_2035_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
stack->m_obj
 = v_res_2035_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_currNamespace_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_currNamespace_2045_);
lean_ctor_set(v___x_2048_, 1, v___y_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_currNamespace_2049_, v___y_2050_, v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2052_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object* v_opts_2053_, lean_object* v_opt_2054_){
_start:
{
lean_object* v_name_2055_; lean_object* v_defValue_2056_; lean_object* v_map_2057_; lean_object* v___x_2058_; 
v_name_2055_ = lean_ctor_get(v_opt_2054_, 0);
v_defValue_2056_ = lean_ctor_get(v_opt_2054_, 1);
v_map_2057_ = lean_ctor_get(v_opts_2053_, 0);
v___x_2058_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2057_, v_name_2055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_unbox(v_defValue_2056_);
return v___x_2059_;
}
else
{
lean_object* v_val_2060_; 
v_val_2060_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v___x_2058_, 1);
if (lean_obj_tag(v_val_2060_) == 1)
{
uint8_t v_v_2061_; 
v_v_2061_ = lean_ctor_get_uint8(v_val_2060_, 0);
lean_dec_ref_known(v_val_2060_, 0);
return v_v_2061_;
}
else
{
uint8_t v___x_2062_; 
lean_dec(v_val_2060_);
v___x_2062_ = lean_unbox(v_defValue_2056_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2053_ = stack[0].m_obj;
lean_object* v_opt_2054_ = stack[1].m_obj;
uint8_t v_res_2063_;
v_res_2063_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_2053_, v_opt_2054_);
stack->m_num = v_res_2063_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object* v_opts_2064_, lean_object* v_opt_2065_){
_start:
{
uint8_t v_res_2066_; lean_object* v_r_2067_; 
v_res_2066_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_2064_, v_opt_2065_);
lean_dec_ref(v_opt_2065_);
lean_dec_ref(v_opts_2064_);
v_r_2067_ = lean_box(v_res_2066_);
return v_r_2067_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_box(1);
v___x_2069_ = l_Lean_MessageData_ofFormat(v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2));
v___x_2074_ = l_Lean_MessageData_ofFormat(v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object* v_x_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
return v_x_2075_;
}
else
{
lean_object* v_head_2077_; lean_object* v_tail_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2100_; 
v_head_2077_ = lean_ctor_get(v_x_2076_, 0);
v_tail_2078_ = lean_ctor_get(v_x_2076_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2080_ = v_x_2076_;
v_isShared_2081_ = v_isSharedCheck_2100_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_tail_2078_);
lean_inc(v_head_2077_);
lean_dec(v_x_2076_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2100_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_before_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2098_; 
v_before_2082_ = lean_ctor_get(v_head_2077_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_head_2077_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_head_2077_, 1);
lean_dec(v_unused_2099_);
v___x_2084_ = v_head_2077_;
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_before_2082_);
lean_dec(v_head_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 7);
lean_ctor_set(v___x_2084_, 1, v___x_2086_);
lean_ctor_set(v___x_2084_, 0, v_x_2075_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_x_2075_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 7);
lean_ctor_set(v___x_2080_, 1, v___x_2089_);
lean_ctor_set(v___x_2080_, 0, v___x_2088_);
v___x_2091_ = v___x_2080_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = l_Lean_MessageData_ofSyntax(v_before_2082_);
v___x_2093_ = l_Lean_indentD(v___x_2092_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2091_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v_x_2075_ = v___x_2094_;
v_x_2076_ = v_tail_2078_;
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
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1));
v___x_2105_ = l_Lean_MessageData_ofFormat(v___x_2104_);
return v___x_2105_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object* v_msgData_2106_, lean_object* v_macroStack_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2110_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2108_);
v___x_2111_ = l_Lean_Elab_pp_macroStack;
v___x_2112_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v___x_2110_, v___x_2111_);
lean_dec_ref(v___x_2110_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_dec(v_macroStack_2107_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v_msgData_2106_);
return v___x_2113_;
}
else
{
if (lean_obj_tag(v_macroStack_2107_) == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_msgData_2106_);
return v___x_2114_;
}
else
{
lean_object* v_head_2115_; lean_object* v_after_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2131_; 
v_head_2115_ = lean_ctor_get(v_macroStack_2107_, 0);
lean_inc(v_head_2115_);
v_after_2116_ = lean_ctor_get(v_head_2115_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_head_2115_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v_head_2115_, 0);
lean_dec(v_unused_2132_);
v___x_2118_ = v_head_2115_;
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_after_2116_);
lean_dec(v_head_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 7);
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
lean_ctor_set(v___x_2118_, 0, v_msgData_2106_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_msgData_2106_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_msgData_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2123_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_MessageData_ofSyntax(v_after_2116_);
v___x_2126_ = l_Lean_indentD(v___x_2125_);
v_msgData_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2127_, 0, v___x_2124_);
lean_ctor_set(v_msgData_2127_, 1, v___x_2126_);
v___x_2128_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_2127_, v_macroStack_2107_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2106_ = stack[0].m_obj;
lean_object* v_macroStack_2107_ = stack[1].m_obj;
lean_object* v___y_2108_ = stack[2].m_obj;
lean_object* v_res_2133_;
v_res_2133_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2106_, v_macroStack_2107_, v___y_2108_);
stack->m_obj
 = v_res_2133_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object* v_msgData_2134_, lean_object* v_macroStack_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2134_, v_macroStack_2135_, v___y_2136_);
lean_dec_ref(v___y_2136_);
return v_res_2138_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_ref_2147_; lean_object* v_macroStack_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
v_ref_2147_ = lean_ctor_get(v___y_2144_, 2);
v_macroStack_2148_ = lean_ctor_get(v___y_2140_, 1);
v___x_2149_ = l_Lean_Elab_getBetterRef(v_ref_2147_, v_macroStack_2148_);
v___x_2150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_2139_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
lean_inc(v_macroStack_2148_);
v___x_2152_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_2151_, v_macroStack_2148_, v___y_2144_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2149_);
lean_ctor_set(v___x_2157_, 1, v_a_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2139_ = stack[0].m_obj;
lean_object* v___y_2140_ = stack[1].m_obj;
lean_object* v___y_2141_ = stack[2].m_obj;
lean_object* v___y_2142_ = stack[3].m_obj;
lean_object* v___y_2143_ = stack[4].m_obj;
lean_object* v___y_2144_ = stack[5].m_obj;
lean_object* v___y_2145_ = stack[6].m_obj;
lean_object* v_res_2162_;
v_res_2162_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
stack->m_obj
 = v_res_2162_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2171_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_toCold_2181_; lean_object* v_currRecDepth_2182_; lean_object* v_ref_2183_; uint16_t v_optionFlags_2184_; uint8_t v_suppressElabErrors_2185_; uint8_t v_isRecordingDeps_2186_; lean_object* v_ref_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_toCold_2181_ = lean_ctor_get(v___y_2178_, 0);
v_currRecDepth_2182_ = lean_ctor_get(v___y_2178_, 1);
v_ref_2183_ = lean_ctor_get(v___y_2178_, 2);
v_optionFlags_2184_ = lean_ctor_get_uint16(v___y_2178_, sizeof(void*)*3);
v_suppressElabErrors_2185_ = lean_ctor_get_uint8(v___y_2178_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2186_ = lean_ctor_get_uint8(v___y_2178_, sizeof(void*)*3 + 3);
v_ref_2187_ = l_Lean_replaceRef(v_ref_2172_, v_ref_2183_);
lean_inc(v_currRecDepth_2182_);
lean_inc_ref(v_toCold_2181_);
v___x_2188_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2188_, 0, v_toCold_2181_);
lean_ctor_set(v___x_2188_, 1, v_currRecDepth_2182_);
lean_ctor_set(v___x_2188_, 2, v_ref_2187_);
lean_ctor_set_uint16(v___x_2188_, sizeof(void*)*3, v_optionFlags_2184_);
lean_ctor_set_uint8(v___x_2188_, sizeof(void*)*3 + 2, v_suppressElabErrors_2185_);
lean_ctor_set_uint8(v___x_2188_, sizeof(void*)*3 + 3, v_isRecordingDeps_2186_);
v___x_2189_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___x_2188_, v___y_2179_);
lean_dec_ref_known(v___x_2188_, 3);
return v___x_2189_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2172_ = stack[0].m_obj;
lean_object* v_msg_2173_ = stack[1].m_obj;
lean_object* v___y_2174_ = stack[2].m_obj;
lean_object* v___y_2175_ = stack[3].m_obj;
lean_object* v___y_2176_ = stack[4].m_obj;
lean_object* v___y_2177_ = stack[5].m_obj;
lean_object* v___y_2178_ = stack[6].m_obj;
lean_object* v___y_2179_ = stack[7].m_obj;
lean_object* v_res_2190_;
v_res_2190_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2172_, v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
stack->m_obj
 = v_res_2190_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2191_, lean_object* v_msg_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2191_, v_msg_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_ref_2191_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2201_, lean_object* v_currNamespace_2202_, lean_object* v_openDecls_2203_, lean_object* v_n_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = l_Lean_ResolveName_resolveNamespace(v_env_2201_, v_currNamespace_2202_, v_openDecls_2203_, v_n_2204_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___y_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2209_, lean_object* v_currNamespace_2210_, lean_object* v_openDecls_2211_, lean_object* v_n_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2209_, v_currNamespace_2210_, v_openDecls_2211_, v_n_2212_, v___y_2213_, v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0(lean_object* v___x_2216_, lean_object* v_entry_2217_, lean_object* v_s_2218_){
_start:
{
lean_object* v_addEntryFn_2219_; lean_object* v_importedEntries_2220_; lean_object* v_state_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2229_; 
v_addEntryFn_2219_ = lean_ctor_get(v___x_2216_, 3);
lean_inc(v_addEntryFn_2219_);
lean_dec_ref(v___x_2216_);
v_importedEntries_2220_ = lean_ctor_get(v_s_2218_, 0);
v_state_2221_ = lean_ctor_get(v_s_2218_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_s_2218_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2223_ = v_s_2218_;
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_state_2221_);
lean_inc(v_importedEntries_2220_);
lean_dec(v_s_2218_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_state_2225_; lean_object* v___x_2227_; 
v_state_2225_ = lean_apply_2(v_addEntryFn_2219_, v_state_2221_, v_entry_2217_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_state_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_importedEntries_2220_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_state_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object* v_keys_2230_, lean_object* v_i_2231_, lean_object* v_k_2232_){
_start:
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = lean_array_get_size(v_keys_2230_);
v___x_2234_ = lean_nat_dec_lt(v_i_2231_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_dec(v_i_2231_);
return v___x_2234_;
}
else
{
lean_object* v_k_x27_2235_; uint8_t v___x_2236_; 
v_k_x27_2235_ = lean_array_fget_borrowed(v_keys_2230_, v_i_2231_);
v___x_2236_ = l_Lean_instBEqExtraModUse_beq(v_k_2232_, v_k_x27_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_i_2231_, v___x_2237_);
lean_dec(v_i_2231_);
v_i_2231_ = v___x_2238_;
goto _start;
}
else
{
lean_dec(v_i_2231_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2230_ = stack[0].m_obj;
lean_object* v_i_2231_ = stack[1].m_obj;
lean_object* v_k_2232_ = stack[2].m_obj;
uint8_t v_res_2240_;
v_res_2240_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2230_, v_i_2231_, v_k_2232_);
stack->m_num = v_res_2240_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object* v_keys_2241_, lean_object* v_i_2242_, lean_object* v_k_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2241_, v_i_2242_, v_k_2243_);
lean_dec_ref(v_k_2243_);
lean_dec_ref(v_keys_2241_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object* v_x_2246_, size_t v_x_2247_, lean_object* v_x_2248_){
_start:
{
if (lean_obj_tag(v_x_2246_) == 0)
{
lean_object* v_es_2249_; lean_object* v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; lean_object* v_j_2253_; lean_object* v___x_2254_; 
v_es_2249_ = lean_ctor_get(v_x_2246_, 0);
v___x_2250_ = lean_box(2);
v___x_2251_ = ((size_t)31ULL);
v___x_2252_ = lean_usize_land(v_x_2247_, v___x_2251_);
v_j_2253_ = lean_usize_to_nat(v___x_2252_);
v___x_2254_ = lean_array_get_borrowed(v___x_2250_, v_es_2249_, v_j_2253_);
lean_dec(v_j_2253_);
switch(lean_obj_tag(v___x_2254_))
{
case 0:
{
lean_object* v_key_2255_; uint8_t v___x_2256_; 
v_key_2255_ = lean_ctor_get(v___x_2254_, 0);
v___x_2256_ = l_Lean_instBEqExtraModUse_beq(v_x_2248_, v_key_2255_);
return v___x_2256_;
}
case 1:
{
lean_object* v_node_2257_; size_t v___x_2258_; size_t v___x_2259_; 
v_node_2257_ = lean_ctor_get(v___x_2254_, 0);
v___x_2258_ = ((size_t)5ULL);
v___x_2259_ = lean_usize_shift_right(v_x_2247_, v___x_2258_);
v_x_2246_ = v_node_2257_;
v_x_2247_ = v___x_2259_;
goto _start;
}
default: 
{
uint8_t v___x_2261_; 
v___x_2261_ = 0;
return v___x_2261_;
}
}
}
else
{
lean_object* v_ks_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v_ks_2262_ = lean_ctor_get(v_x_2246_, 0);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_2262_, v___x_2263_, v_x_2248_);
return v___x_2264_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2246_ = stack[0].m_obj;
size_t v_x_2247_ = stack[1].m_num;
lean_object* v_x_2248_ = stack[2].m_obj;
uint8_t v_res_2265_;
v_res_2265_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2246_, v_x_2247_, v_x_2248_);
stack->m_num = v_res_2265_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_){
_start:
{
size_t v_x_31252__boxed_2269_; uint8_t v_res_2270_; lean_object* v_r_2271_; 
v_x_31252__boxed_2269_ = lean_unbox_usize(v_x_2267_);
lean_dec(v_x_2267_);
v_res_2270_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2266_, v_x_31252__boxed_2269_, v_x_2268_);
lean_dec_ref(v_x_2268_);
lean_dec_ref(v_x_2266_);
v_r_2271_ = lean_box(v_res_2270_);
return v_r_2271_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object* v_x_2272_, lean_object* v_x_2273_){
_start:
{
uint64_t v___x_2274_; size_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = l_Lean_instHashableExtraModUse_hash(v_x_2273_);
v___x_2275_ = lean_uint64_to_usize(v___x_2274_);
v___x_2276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2272_, v___x_2275_, v_x_2273_);
return v___x_2276_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2272_ = stack[0].m_obj;
lean_object* v_x_2273_ = stack[1].m_obj;
uint8_t v_res_2277_;
v_res_2277_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2272_, v_x_2273_);
stack->m_num = v_res_2277_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
uint8_t v_res_2280_; lean_object* v_r_2281_; 
v_res_2280_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2278_, v_x_2279_);
lean_dec_ref(v_x_2279_);
lean_dec_ref(v_x_2278_);
v_r_2281_ = lean_box(v_res_2280_);
return v_r_2281_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2282_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v_cls_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_cls_2294_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2295_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2296_ = l_Lean_Name_append(v___x_2295_, v_cls_2294_);
return v___x_2296_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2307_, uint8_t v_isMeta_2308_, lean_object* v_hint_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_env_2351_; uint8_t v_isExporting_2352_; lean_object* v_entry_2353_; lean_object* v___x_2354_; lean_object* v_env_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2349_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0);
v___x_2350_ = lean_st_ref_get(v___y_2315_);
v_env_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc_ref(v_env_2351_);
lean_dec(v___x_2350_);
v_isExporting_2352_ = lean_ctor_get_uint8(v_env_2351_, sizeof(void*)*13);
lean_dec_ref(v_env_2351_);
lean_inc(v_mod_2307_);
v_entry_2353_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2353_, 0, v_mod_2307_);
lean_ctor_set_uint8(v_entry_2353_, sizeof(void*)*1, v_isExporting_2352_);
lean_ctor_set_uint8(v_entry_2353_, sizeof(void*)*1 + 1, v_isMeta_2308_);
v___x_2354_ = lean_st_ref_get(v___y_2315_);
v_env_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc_ref(v_env_2355_);
lean_dec(v___x_2354_);
v___x_2356_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2357_ = lean_box(1);
v___x_2358_ = lean_box(0);
v___x_2359_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2349_, v___x_2356_, v_env_2355_, v___x_2357_, v___x_2358_);
v___x_2360_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_2359_, v_entry_2353_);
lean_dec(v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v_toCold_2361_; lean_object* v_options_2362_; lean_object* v_inheritedTraceOptions_2363_; uint8_t v_hasTrace_2364_; lean_object* v___f_2365_; uint8_t v___x_2366_; lean_object* v___y_2368_; lean_object* v___y_2369_; 
v_toCold_2361_ = lean_ctor_get(v___y_2314_, 0);
v_options_2362_ = lean_ctor_get(v_toCold_2361_, 2);
v_inheritedTraceOptions_2363_ = lean_ctor_get(v_toCold_2361_, 11);
v_hasTrace_2364_ = lean_ctor_get_uint8(v_options_2362_, sizeof(void*)*1);
v___f_2365_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_2365_, 0, v___x_2356_);
lean_closure_set(v___f_2365_, 1, v_entry_2353_);
v___x_2366_ = 1;
if (v_hasTrace_2364_ == 0)
{
lean_dec(v_hint_2309_);
lean_dec(v_mod_2307_);
v___y_2368_ = v___y_2313_;
v___y_2369_ = v___y_2315_;
goto v___jp_2367_;
}
else
{
lean_object* v_cls_2396_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v_cls_2396_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2416_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2417_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2363_, v_options_2362_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_dec(v_hint_2309_);
lean_dec(v_mod_2307_);
v___y_2368_ = v___y_2313_;
v___y_2369_ = v___y_2315_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2418_; lean_object* v___y_2420_; 
v___x_2418_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
if (v_isExporting_2352_ == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2420_ = v___x_2427_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2428_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2420_ = v___x_2428_;
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_inc_ref(v___y_2420_);
v___x_2421_ = l_Lean_stringToMessageData(v___y_2420_);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2418_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
if (v_isMeta_2308_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___y_2403_ = v___x_2424_;
v___y_2404_ = v___x_2425_;
goto v___jp_2402_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14));
v___y_2403_ = v___x_2424_;
v___y_2404_ = v___x_2426_;
goto v___jp_2402_;
}
}
}
v___jp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___y_2398_);
lean_ctor_set(v___x_2400_, 1, v___y_2399_);
v___x_2401_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2396_, v___x_2400_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_dec_ref_known(v___x_2401_, 1);
v___y_2368_ = v___y_2313_;
v___y_2369_ = v___y_2315_;
goto v___jp_2367_;
}
else
{
lean_dec_ref(v___f_2365_);
return v___x_2401_;
}
}
v___jp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
lean_inc_ref(v___y_2404_);
v___x_2405_ = l_Lean_stringToMessageData(v___y_2404_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___y_2403_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4);
v___x_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Lean_MessageData_ofName(v_mod_2307_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l_Lean_Name_isAnonymous(v_hint_2309_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2413_ = l_Lean_MessageData_ofName(v_hint_2309_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___y_2398_ = v___x_2410_;
v___y_2399_ = v___x_2414_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2415_; 
lean_dec(v_hint_2309_);
v___x_2415_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7);
v___y_2398_ = v___x_2410_;
v___y_2399_ = v___x_2415_;
goto v___jp_2397_;
}
}
}
v___jp_2367_:
{
lean_object* v___x_2370_; lean_object* v_toEnvExtension_2371_; uint8_t v_logWrites_2372_; 
v___x_2370_ = lean_st_ref_take(v___y_2369_);
v_toEnvExtension_2371_ = lean_ctor_get(v___x_2356_, 0);
v_logWrites_2372_ = lean_ctor_get_uint8(v_toEnvExtension_2371_, sizeof(void*)*6);
if (v_logWrites_2372_ == 0)
{
lean_object* v_env_2373_; lean_object* v_nextMacroScope_2374_; lean_object* v_ngen_2375_; lean_object* v_auxDeclNGen_2376_; lean_object* v_traceState_2377_; lean_object* v_recordedDeps_2378_; lean_object* v_messages_2379_; lean_object* v_infoState_2380_; lean_object* v_snapshotTasks_2381_; lean_object* v_asyncMode_2382_; lean_object* v___x_2383_; 
v_env_2373_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_ref(v_env_2373_);
v_nextMacroScope_2374_ = lean_ctor_get(v___x_2370_, 1);
lean_inc(v_nextMacroScope_2374_);
v_ngen_2375_ = lean_ctor_get(v___x_2370_, 2);
lean_inc_ref(v_ngen_2375_);
v_auxDeclNGen_2376_ = lean_ctor_get(v___x_2370_, 3);
lean_inc_ref(v_auxDeclNGen_2376_);
v_traceState_2377_ = lean_ctor_get(v___x_2370_, 4);
lean_inc_ref(v_traceState_2377_);
v_recordedDeps_2378_ = lean_ctor_get(v___x_2370_, 6);
lean_inc_ref(v_recordedDeps_2378_);
v_messages_2379_ = lean_ctor_get(v___x_2370_, 7);
lean_inc_ref(v_messages_2379_);
v_infoState_2380_ = lean_ctor_get(v___x_2370_, 8);
lean_inc_ref(v_infoState_2380_);
v_snapshotTasks_2381_ = lean_ctor_get(v___x_2370_, 9);
lean_inc_ref(v_snapshotTasks_2381_);
lean_dec(v___x_2370_);
v_asyncMode_2382_ = lean_ctor_get(v_toEnvExtension_2371_, 2);
lean_inc_ref(v_toEnvExtension_2371_);
v___x_2383_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2371_, v_env_2373_, v___f_2365_, v_asyncMode_2382_, v___x_2358_, v___x_2366_);
v___y_2318_ = v_ngen_2375_;
v___y_2319_ = v_snapshotTasks_2381_;
v___y_2320_ = v_nextMacroScope_2374_;
v___y_2321_ = v___y_2369_;
v___y_2322_ = v_messages_2379_;
v___y_2323_ = v_recordedDeps_2378_;
v___y_2324_ = v_infoState_2380_;
v___y_2325_ = v___y_2368_;
v___y_2326_ = v_traceState_2377_;
v___y_2327_ = v_auxDeclNGen_2376_;
v___y_2328_ = v___x_2383_;
goto v___jp_2317_;
}
else
{
lean_object* v_env_2384_; lean_object* v_nextMacroScope_2385_; lean_object* v_ngen_2386_; lean_object* v_auxDeclNGen_2387_; lean_object* v_traceState_2388_; lean_object* v_recordedDeps_2389_; lean_object* v_messages_2390_; lean_object* v_infoState_2391_; lean_object* v_snapshotTasks_2392_; lean_object* v_asyncMode_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_env_2384_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_ref(v_env_2384_);
v_nextMacroScope_2385_ = lean_ctor_get(v___x_2370_, 1);
lean_inc(v_nextMacroScope_2385_);
v_ngen_2386_ = lean_ctor_get(v___x_2370_, 2);
lean_inc_ref(v_ngen_2386_);
v_auxDeclNGen_2387_ = lean_ctor_get(v___x_2370_, 3);
lean_inc_ref(v_auxDeclNGen_2387_);
v_traceState_2388_ = lean_ctor_get(v___x_2370_, 4);
lean_inc_ref(v_traceState_2388_);
v_recordedDeps_2389_ = lean_ctor_get(v___x_2370_, 6);
lean_inc_ref(v_recordedDeps_2389_);
v_messages_2390_ = lean_ctor_get(v___x_2370_, 7);
lean_inc_ref(v_messages_2390_);
v_infoState_2391_ = lean_ctor_get(v___x_2370_, 8);
lean_inc_ref(v_infoState_2391_);
v_snapshotTasks_2392_ = lean_ctor_get(v___x_2370_, 9);
lean_inc_ref(v_snapshotTasks_2392_);
lean_dec(v___x_2370_);
v_asyncMode_2393_ = lean_ctor_get(v_toEnvExtension_2371_, 2);
lean_inc_ref_n(v_toEnvExtension_2371_, 2);
v___x_2394_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2371_, v_env_2384_);
lean_dec_ref(v_env_2384_);
v___x_2395_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2371_, v___x_2394_, v___f_2365_, v_asyncMode_2393_, v___x_2358_, v___x_2366_);
v___y_2318_ = v_ngen_2386_;
v___y_2319_ = v_snapshotTasks_2392_;
v___y_2320_ = v_nextMacroScope_2385_;
v___y_2321_ = v___y_2369_;
v___y_2322_ = v_messages_2390_;
v___y_2323_ = v_recordedDeps_2389_;
v___y_2324_ = v_infoState_2391_;
v___y_2325_ = v___y_2368_;
v___y_2326_ = v_traceState_2388_;
v___y_2327_ = v_auxDeclNGen_2387_;
v___y_2328_ = v___x_2395_;
goto v___jp_2317_;
}
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec_ref_known(v_entry_2353_, 1);
lean_dec(v_hint_2309_);
lean_dec(v_mod_2307_);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
v___jp_2317_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_mctx_2333_; lean_object* v_zetaDeltaFVarIds_2334_; lean_object* v_postponed_2335_; lean_object* v_diag_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2347_; 
v___x_2329_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
v___x_2330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2330_, 0, v___y_2328_);
lean_ctor_set(v___x_2330_, 1, v___y_2320_);
lean_ctor_set(v___x_2330_, 2, v___y_2318_);
lean_ctor_set(v___x_2330_, 3, v___y_2327_);
lean_ctor_set(v___x_2330_, 4, v___y_2326_);
lean_ctor_set(v___x_2330_, 5, v___x_2329_);
lean_ctor_set(v___x_2330_, 6, v___y_2323_);
lean_ctor_set(v___x_2330_, 7, v___y_2322_);
lean_ctor_set(v___x_2330_, 8, v___y_2324_);
lean_ctor_set(v___x_2330_, 9, v___y_2319_);
v___x_2331_ = lean_st_ref_put(v___y_2321_, v___x_2330_);
v___x_2332_ = lean_st_ref_take(v___y_2325_);
v_mctx_2333_ = lean_ctor_get(v___x_2332_, 0);
v_zetaDeltaFVarIds_2334_ = lean_ctor_get(v___x_2332_, 2);
v_postponed_2335_ = lean_ctor_get(v___x_2332_, 3);
v_diag_2336_ = lean_ctor_get(v___x_2332_, 4);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2332_, 1);
lean_dec(v_unused_2348_);
v___x_2338_ = v___x_2332_;
v_isShared_2339_ = v_isSharedCheck_2347_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_diag_2336_);
lean_inc(v_postponed_2335_);
lean_inc(v_zetaDeltaFVarIds_2334_);
lean_inc(v_mctx_2333_);
lean_dec(v___x_2332_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2347_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v___x_2341_);
v___x_2343_ = v___x_2338_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_mctx_2333_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_zetaDeltaFVarIds_2334_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_postponed_2335_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_diag_2336_);
v___x_2343_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_st_ref_put(v___y_2325_, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2340_);
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_2307_ = stack[0].m_obj;
uint8_t v_isMeta_2308_ = stack[1].m_num;
lean_object* v_hint_2309_ = stack[2].m_obj;
lean_object* v___y_2310_ = stack[3].m_obj;
lean_object* v___y_2311_ = stack[4].m_obj;
lean_object* v___y_2312_ = stack[5].m_obj;
lean_object* v___y_2313_ = stack[6].m_obj;
lean_object* v___y_2314_ = stack[7].m_obj;
lean_object* v___y_2315_ = stack[8].m_obj;
lean_object* v_res_2431_;
v_res_2431_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2307_, v_isMeta_2308_, v_hint_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
stack->m_obj
 = v_res_2431_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2432_, lean_object* v_isMeta_2433_, lean_object* v_hint_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
uint8_t v_isMeta_boxed_2442_; lean_object* v_res_2443_; 
v_isMeta_boxed_2442_ = lean_unbox(v_isMeta_2433_);
v_res_2443_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2432_, v_isMeta_boxed_2442_, v_hint_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
return v_res_2443_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2444_, lean_object* v_declName_2445_, lean_object* v_as_2446_, size_t v_sz_2447_, size_t v_i_2448_, lean_object* v_b_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
uint8_t v___x_2457_; 
v___x_2457_ = lean_usize_dec_lt(v_i_2448_, v_sz_2447_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
lean_dec(v_declName_2445_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_b_2449_);
return v___x_2458_;
}
else
{
lean_object* v___x_2459_; lean_object* v_modules_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2463_; lean_object* v_toImport_2464_; lean_object* v_module_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2459_ = l_Lean_Environment_header(v___x_2444_);
v_modules_2460_ = lean_ctor_get(v___x_2459_, 3);
lean_inc_ref(v_modules_2460_);
lean_dec_ref(v___x_2459_);
v___x_2461_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2462_ = lean_array_uget_borrowed(v_as_2446_, v_i_2448_);
v___x_2463_ = lean_array_get(v___x_2461_, v_modules_2460_, v_a_2462_);
lean_dec_ref(v_modules_2460_);
v_toImport_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_ref(v_toImport_2464_);
lean_dec(v___x_2463_);
v_module_2465_ = lean_ctor_get(v_toImport_2464_, 0);
lean_inc(v_module_2465_);
lean_dec_ref(v_toImport_2464_);
v___x_2466_ = lean_box(0);
v___x_2467_ = 0;
lean_inc(v_declName_2445_);
v___x_2468_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2465_, v___x_2467_, v_declName_2445_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2468_) == 0)
{
size_t v___x_2469_; size_t v___x_2470_; 
lean_dec_ref_known(v___x_2468_, 1);
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_add(v_i_2448_, v___x_2469_);
v_i_2448_ = v___x_2470_;
v_b_2449_ = v___x_2466_;
goto _start;
}
else
{
lean_dec(v_declName_2445_);
return v___x_2468_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2444_ = stack[0].m_obj;
lean_object* v_declName_2445_ = stack[1].m_obj;
lean_object* v_as_2446_ = stack[2].m_obj;
size_t v_sz_2447_ = stack[3].m_num;
size_t v_i_2448_ = stack[4].m_num;
lean_object* v_b_2449_ = stack[5].m_obj;
lean_object* v___y_2450_ = stack[6].m_obj;
lean_object* v___y_2451_ = stack[7].m_obj;
lean_object* v___y_2452_ = stack[8].m_obj;
lean_object* v___y_2453_ = stack[9].m_obj;
lean_object* v___y_2454_ = stack[10].m_obj;
lean_object* v___y_2455_ = stack[11].m_obj;
lean_object* v_res_2472_;
v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2444_, v_declName_2445_, v_as_2446_, v_sz_2447_, v_i_2448_, v_b_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
stack->m_obj
 = v_res_2472_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2473_, lean_object* v_declName_2474_, lean_object* v_as_2475_, lean_object* v_sz_2476_, lean_object* v_i_2477_, lean_object* v_b_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2476_);
lean_dec(v_sz_2476_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2477_);
lean_dec(v_i_2477_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2473_, v_declName_2474_, v_as_2475_, v_sz_boxed_2486_, v_i_boxed_2487_, v_b_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_as_2475_);
lean_dec_ref(v___x_2473_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object* v_a_2489_, lean_object* v_x_2490_){
_start:
{
if (lean_obj_tag(v_x_2490_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
else
{
lean_object* v_key_2492_; lean_object* v_value_2493_; lean_object* v_tail_2494_; uint8_t v___x_2495_; 
v_key_2492_ = lean_ctor_get(v_x_2490_, 0);
v_value_2493_ = lean_ctor_get(v_x_2490_, 1);
v_tail_2494_ = lean_ctor_get(v_x_2490_, 2);
v___x_2495_ = lean_name_eq(v_key_2492_, v_a_2489_);
if (v___x_2495_ == 0)
{
v_x_2490_ = v_tail_2494_;
goto _start;
}
else
{
lean_object* v___x_2497_; 
lean_inc(v_value_2493_);
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_value_2493_);
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object* v_a_2498_, lean_object* v_x_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2498_, v_x_2499_);
lean_dec(v_x_2499_);
lean_dec(v_a_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_buckets_2503_; lean_object* v___x_2504_; uint64_t v___y_2506_; 
v_buckets_2503_ = lean_ctor_get(v_m_2501_, 1);
v___x_2504_ = lean_array_get_size(v_buckets_2503_);
if (lean_obj_tag(v_a_2502_) == 0)
{
uint64_t v___x_2520_; 
v___x_2520_ = 1723ULL;
v___y_2506_ = v___x_2520_;
goto v___jp_2505_;
}
else
{
uint64_t v_hash_2521_; 
v_hash_2521_ = lean_ctor_get_uint64(v_a_2502_, sizeof(void*)*2);
v___y_2506_ = v_hash_2521_;
goto v___jp_2505_;
}
v___jp_2505_:
{
uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v_fold_2509_; uint64_t v___x_2510_; uint64_t v___x_2511_; uint64_t v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2507_ = 32ULL;
v___x_2508_ = lean_uint64_shift_right(v___y_2506_, v___x_2507_);
v_fold_2509_ = lean_uint64_xor(v___y_2506_, v___x_2508_);
v___x_2510_ = 16ULL;
v___x_2511_ = lean_uint64_shift_right(v_fold_2509_, v___x_2510_);
v___x_2512_ = lean_uint64_xor(v_fold_2509_, v___x_2511_);
v___x_2513_ = lean_uint64_to_usize(v___x_2512_);
v___x_2514_ = lean_usize_of_nat(v___x_2504_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_sub(v___x_2514_, v___x_2515_);
v___x_2517_ = lean_usize_land(v___x_2513_, v___x_2516_);
v___x_2518_ = lean_array_uget_borrowed(v_buckets_2503_, v___x_2517_);
v___x_2519_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2502_, v___x_2518_);
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2522_, v_a_2523_);
lean_dec(v_a_2523_);
lean_dec_ref(v_m_2522_);
return v_res_2524_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2525_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2528_, uint8_t v_isMeta_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_env_2542_; lean_object* v___y_2544_; lean_object* v___x_2557_; 
v___x_2537_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0);
v___x_2538_ = lean_st_ref_get(v___y_2535_);
v_env_2542_ = lean_ctor_get(v___x_2538_, 0);
lean_inc_ref(v_env_2542_);
lean_dec(v___x_2538_);
v___x_2557_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2542_, v_declName_2528_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_dec_ref(v_env_2542_);
lean_dec(v_declName_2528_);
goto v___jp_2539_;
}
else
{
lean_object* v_val_2558_; lean_object* v___x_2559_; lean_object* v_modules_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v_val_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = l_Lean_Environment_header(v_env_2542_);
v_modules_2560_ = lean_ctor_get(v___x_2559_, 3);
lean_inc_ref(v_modules_2560_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = lean_array_get_size(v_modules_2560_);
v___x_2562_ = lean_nat_dec_lt(v_val_2558_, v___x_2561_);
if (v___x_2562_ == 0)
{
lean_dec_ref(v_modules_2560_);
lean_dec(v_val_2558_);
lean_dec_ref(v_env_2542_);
lean_dec(v_declName_2528_);
goto v___jp_2539_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___y_2566_; 
v___x_2563_ = lean_array_fget(v_modules_2560_, v_val_2558_);
lean_dec(v_val_2558_);
lean_dec_ref(v_modules_2560_);
v___x_2564_ = lean_st_ref_get(v___y_2535_);
if (v_isMeta_2529_ == 0)
{
lean_dec(v___x_2564_);
v___y_2566_ = v_isMeta_2529_;
goto v___jp_2565_;
}
else
{
lean_object* v_env_2577_; uint8_t v___x_2578_; 
v_env_2577_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_env_2577_);
lean_dec(v___x_2564_);
lean_inc(v_declName_2528_);
v___x_2578_ = l_Lean_isMarkedMeta(v_env_2577_, v_declName_2528_);
if (v___x_2578_ == 0)
{
v___y_2566_ = v_isMeta_2529_;
goto v___jp_2565_;
}
else
{
uint8_t v___x_2579_; 
v___x_2579_ = 0;
v___y_2566_ = v___x_2579_;
goto v___jp_2565_;
}
}
v___jp_2565_:
{
lean_object* v_toImport_2567_; lean_object* v_module_2568_; lean_object* v___x_2569_; 
v_toImport_2567_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_ref(v_toImport_2567_);
lean_dec(v___x_2563_);
v_module_2568_ = lean_ctor_get(v_toImport_2567_, 0);
lean_inc(v_module_2568_);
lean_dec_ref(v_toImport_2567_);
lean_inc(v_declName_2528_);
v___x_2569_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2568_, v___y_2566_, v_declName_2528_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref_known(v___x_2569_, 1);
v___x_2570_ = l_Lean_indirectModUseExt;
v___x_2571_ = lean_box(1);
v___x_2572_ = lean_box(0);
lean_inc_ref(v_env_2542_);
v___x_2573_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2537_, v___x_2570_, v_env_2542_, v___x_2571_, v___x_2572_);
v___x_2574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2573_, v_declName_2528_);
lean_dec(v___x_2573_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___y_2544_ = v___x_2575_;
goto v___jp_2543_;
}
else
{
lean_object* v_val_2576_; 
v_val_2576_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_val_2576_);
lean_dec_ref_known(v___x_2574_, 1);
v___y_2544_ = v_val_2576_;
goto v___jp_2543_;
}
}
else
{
lean_dec_ref(v_env_2542_);
lean_dec(v_declName_2528_);
return v___x_2569_;
}
}
}
}
v___jp_2539_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
v___jp_2543_:
{
lean_object* v___x_2545_; size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2545_ = lean_box(0);
v_sz_2546_ = lean_array_size(v___y_2544_);
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2542_, v_declName_2528_, v___y_2544_, v_sz_2546_, v___x_2547_, v___x_2545_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_env_2542_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v___x_2548_, 0);
lean_dec(v_unused_2556_);
v___x_2550_ = v___x_2548_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_dec(v___x_2548_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2545_);
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2545_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
return v___x_2548_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2528_ = stack[0].m_obj;
uint8_t v_isMeta_2529_ = stack[1].m_num;
lean_object* v___y_2530_ = stack[2].m_obj;
lean_object* v___y_2531_ = stack[3].m_obj;
lean_object* v___y_2532_ = stack[4].m_obj;
lean_object* v___y_2533_ = stack[5].m_obj;
lean_object* v___y_2534_ = stack[6].m_obj;
lean_object* v___y_2535_ = stack[7].m_obj;
lean_object* v_res_2580_;
v_res_2580_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2528_, v_isMeta_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
stack->m_obj
 = v_res_2580_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2581_, lean_object* v_isMeta_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v_isMeta_boxed_2590_; lean_object* v_res_2591_; 
v_isMeta_boxed_2590_ = lean_unbox(v_isMeta_2582_);
v_res_2591_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2581_, v_isMeta_boxed_2590_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2591_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
if (lean_obj_tag(v_as_x27_2592_) == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_b_2593_);
return v___x_2601_;
}
else
{
lean_object* v_head_2602_; lean_object* v_tail_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; 
v_head_2602_ = lean_ctor_get(v_as_x27_2592_, 0);
v_tail_2603_ = lean_ctor_get(v_as_x27_2592_, 1);
v___x_2604_ = lean_box(0);
v___x_2605_ = 1;
lean_inc(v_head_2602_);
v___x_2606_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2602_, v___x_2605_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_dec_ref_known(v___x_2606_, 1);
v_as_x27_2592_ = v_tail_2603_;
v_b_2593_ = v___x_2604_;
goto _start;
}
else
{
return v___x_2606_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2592_ = stack[0].m_obj;
lean_object* v_b_2593_ = stack[1].m_obj;
lean_object* v___y_2594_ = stack[2].m_obj;
lean_object* v___y_2595_ = stack[3].m_obj;
lean_object* v___y_2596_ = stack[4].m_obj;
lean_object* v___y_2597_ = stack[5].m_obj;
lean_object* v___y_2598_ = stack[6].m_obj;
lean_object* v___y_2599_ = stack[7].m_obj;
lean_object* v_res_2608_;
v_res_2608_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2592_, v_b_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
stack->m_obj
 = v_res_2608_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2609_, lean_object* v_b_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2609_, v_b_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v_as_x27_2609_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_env_2619_, lean_object* v___x_2620_, lean_object* v_currNamespace_2621_, lean_object* v_openDecls_2622_, lean_object* v_n_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = l_Lean_ResolveName_resolveGlobalName(v_env_2619_, v___x_2620_, v_currNamespace_2621_, v_openDecls_2622_, v_n_2623_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___y_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_env_2628_, lean_object* v___x_2629_, lean_object* v_currNamespace_2630_, lean_object* v_openDecls_2631_, lean_object* v_n_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_env_2628_, v___x_2629_, v_currNamespace_2630_, v_openDecls_2631_, v_n_2632_, v___y_2633_, v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2629_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2636_, lean_object* v_declName_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
uint8_t v___x_2640_; lean_object* v_env_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; uint8_t v___x_2644_; 
v___x_2640_ = 0;
v_env_2641_ = l_Lean_Environment_setExporting(v_env_2636_, v___x_2640_);
lean_inc(v_declName_2637_);
v___x_2642_ = l_Lean_mkPrivateName(v_env_2641_, v_declName_2637_);
v___x_2643_ = 1;
lean_inc_ref(v_env_2641_);
v___x_2644_ = l_Lean_Environment_contains(v_env_2641_, v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = l_Lean_privateToUserName(v_declName_2637_);
v___x_2646_ = l_Lean_Environment_contains(v_env_2641_, v___x_2645_, v___x_2643_);
v___x_2647_ = lean_box(v___x_2646_);
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___y_2639_);
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec_ref(v_env_2641_);
lean_dec(v_declName_2637_);
v___x_2649_ = lean_box(v___x_2644_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___y_2639_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2651_, lean_object* v_declName_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2651_, v_declName_2652_, v___y_2653_, v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2655_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = l_Lean_maxRecDepthErrorMessage;
v___x_2662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2664_ = l_Lean_MessageData_ofFormat(v___x_2663_);
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2666_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2667_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v___x_2665_);
return v___x_2667_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_ref_2668_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2668_ = stack[0].m_obj;
lean_object* v_res_2673_;
v_res_2673_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2668_);
stack->m_obj
 = v_res_2673_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2674_);
return v_res_2676_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; lean_object* v_toCold_2687_; lean_object* v_env_2688_; lean_object* v_currRecDepth_2689_; lean_object* v_ref_2690_; lean_object* v_maxRecDepth_2691_; lean_object* v_currNamespace_2692_; lean_object* v_openDecls_2693_; lean_object* v_quotContext_2694_; lean_object* v_currMacroScope_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; lean_object* v_methods_2702_; lean_object* v___x_2703_; lean_object* v_nextMacroScope_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2686_ = lean_st_ref_get(v___y_2684_);
v_toCold_2687_ = lean_ctor_get(v___y_2683_, 0);
v_env_2688_ = lean_ctor_get(v___x_2686_, 0);
lean_inc_ref_n(v_env_2688_, 4);
lean_dec(v___x_2686_);
v_currRecDepth_2689_ = lean_ctor_get(v___y_2683_, 1);
v_ref_2690_ = lean_ctor_get(v___y_2683_, 2);
v_maxRecDepth_2691_ = lean_ctor_get(v_toCold_2687_, 3);
v_currNamespace_2692_ = lean_ctor_get(v_toCold_2687_, 4);
v_openDecls_2693_ = lean_ctor_get(v_toCold_2687_, 5);
v_quotContext_2694_ = lean_ctor_get(v_toCold_2687_, 8);
v_currMacroScope_2695_ = lean_ctor_get(v_toCold_2687_, 9);
v___f_2696_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2696_, 0, v_env_2688_);
v___f_2697_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2697_, 0, v_env_2688_);
v___x_2698_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2683_);
lean_inc_n(v_currNamespace_2692_, 3);
v___f_2699_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2699_, 0, v_currNamespace_2692_);
lean_inc_n(v_openDecls_2693_, 2);
v___f_2700_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2700_, 0, v_env_2688_);
lean_closure_set(v___f_2700_, 1, v___x_2698_);
lean_closure_set(v___f_2700_, 2, v_currNamespace_2692_);
lean_closure_set(v___f_2700_, 3, v_openDecls_2693_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2701_, 0, v_env_2688_);
lean_closure_set(v___f_2701_, 1, v_currNamespace_2692_);
lean_closure_set(v___f_2701_, 2, v_openDecls_2693_);
v_methods_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2702_, 0, v___f_2697_);
lean_ctor_set(v_methods_2702_, 1, v___f_2699_);
lean_ctor_set(v_methods_2702_, 2, v___f_2696_);
lean_ctor_set(v_methods_2702_, 3, v___f_2701_);
lean_ctor_set(v_methods_2702_, 4, v___f_2700_);
v___x_2703_ = lean_st_ref_get(v___y_2684_);
v_nextMacroScope_2704_ = lean_ctor_get(v___x_2703_, 1);
lean_inc(v_nextMacroScope_2704_);
lean_dec(v___x_2703_);
lean_inc(v_ref_2690_);
lean_inc(v_maxRecDepth_2691_);
lean_inc(v_currRecDepth_2689_);
lean_inc(v_currMacroScope_2695_);
lean_inc(v_quotContext_2694_);
v___x_2705_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2705_, 0, v_methods_2702_);
lean_ctor_set(v___x_2705_, 1, v_quotContext_2694_);
lean_ctor_set(v___x_2705_, 2, v_currMacroScope_2695_);
lean_ctor_set(v___x_2705_, 3, v_currRecDepth_2689_);
lean_ctor_set(v___x_2705_, 4, v_maxRecDepth_2691_);
lean_ctor_set(v___x_2705_, 5, v_ref_2690_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2707_, 0, v_nextMacroScope_2704_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
lean_ctor_set(v___x_2707_, 2, v___x_2706_);
v___x_2708_ = lean_apply_2(v_x_2678_, v___x_2705_, v___x_2707_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v_a_2710_; lean_object* v_macroScope_2711_; lean_object* v_traceMsgs_2712_; lean_object* v_expandedMacroDecls_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 1);
lean_inc(v_a_2709_);
v_a_2710_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2708_, 2);
v_macroScope_2711_ = lean_ctor_get(v_a_2709_, 0);
lean_inc(v_macroScope_2711_);
v_traceMsgs_2712_ = lean_ctor_get(v_a_2709_, 1);
lean_inc(v_traceMsgs_2712_);
v_expandedMacroDecls_2713_ = lean_ctor_get(v_a_2709_, 2);
lean_inc(v_expandedMacroDecls_2713_);
lean_dec(v_a_2709_);
v___x_2714_ = lean_box(0);
v___x_2715_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2713_, v___x_2714_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v_expandedMacroDecls_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v___x_2716_; lean_object* v_env_2717_; lean_object* v_ngen_2718_; lean_object* v_auxDeclNGen_2719_; lean_object* v_traceState_2720_; lean_object* v_cache_2721_; lean_object* v_recordedDeps_2722_; lean_object* v_messages_2723_; lean_object* v_infoState_2724_; lean_object* v_snapshotTasks_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref_known(v___x_2715_, 1);
v___x_2716_ = lean_st_ref_take(v___y_2684_);
v_env_2717_ = lean_ctor_get(v___x_2716_, 0);
v_ngen_2718_ = lean_ctor_get(v___x_2716_, 2);
v_auxDeclNGen_2719_ = lean_ctor_get(v___x_2716_, 3);
v_traceState_2720_ = lean_ctor_get(v___x_2716_, 4);
v_cache_2721_ = lean_ctor_get(v___x_2716_, 5);
v_recordedDeps_2722_ = lean_ctor_get(v___x_2716_, 6);
v_messages_2723_ = lean_ctor_get(v___x_2716_, 7);
v_infoState_2724_ = lean_ctor_get(v___x_2716_, 8);
v_snapshotTasks_2725_ = lean_ctor_get(v___x_2716_, 9);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v___x_2716_, 1);
lean_dec(v_unused_2752_);
v___x_2727_ = v___x_2716_;
v_isShared_2728_ = v_isSharedCheck_2751_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_snapshotTasks_2725_);
lean_inc(v_infoState_2724_);
lean_inc(v_messages_2723_);
lean_inc(v_recordedDeps_2722_);
lean_inc(v_cache_2721_);
lean_inc(v_traceState_2720_);
lean_inc(v_auxDeclNGen_2719_);
lean_inc(v_ngen_2718_);
lean_inc(v_env_2717_);
lean_dec(v___x_2716_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2751_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 1, v_macroScope_2711_);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_env_2717_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_macroScope_2711_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_ngen_2718_);
lean_ctor_set(v_reuseFailAlloc_2750_, 3, v_auxDeclNGen_2719_);
lean_ctor_set(v_reuseFailAlloc_2750_, 4, v_traceState_2720_);
lean_ctor_set(v_reuseFailAlloc_2750_, 5, v_cache_2721_);
lean_ctor_set(v_reuseFailAlloc_2750_, 6, v_recordedDeps_2722_);
lean_ctor_set(v_reuseFailAlloc_2750_, 7, v_messages_2723_);
lean_ctor_set(v_reuseFailAlloc_2750_, 8, v_infoState_2724_);
lean_ctor_set(v_reuseFailAlloc_2750_, 9, v_snapshotTasks_2725_);
v___x_2730_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = lean_st_ref_put(v___y_2684_, v___x_2730_);
v___x_2732_ = l_List_reverse___redArg(v_traceMsgs_2712_);
v___x_2733_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2732_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; 
v_unused_2741_ = lean_ctor_get(v___x_2733_, 0);
lean_dec(v_unused_2741_);
v___x_2735_ = v___x_2733_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_dec(v___x_2733_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_a_2710_);
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2710_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_a_2710_);
v_a_2742_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2733_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2733_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_traceMsgs_2712_);
lean_dec(v_macroScope_2711_);
lean_dec(v_a_2710_);
v_a_2753_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2715_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2715_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2708_, 2);
if (lean_obj_tag(v_a_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v_a_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_a_2762_ = lean_ctor_get(v_a_2761_, 0);
lean_inc(v_a_2762_);
v_a_2763_ = lean_ctor_get(v_a_2761_, 1);
lean_inc_ref(v_a_2763_);
lean_dec_ref_known(v_a_2761_, 2);
v___x_2764_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2765_ = lean_string_dec_eq(v_a_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_a_2763_);
v___x_2767_ = l_Lean_MessageData_ofFormat(v___x_2766_);
v___x_2768_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2762_, v___x_2767_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v_a_2762_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; 
lean_dec_ref(v_a_2763_);
v___x_2769_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2762_);
return v___x_2769_;
}
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2770_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2678_ = stack[0].m_obj;
lean_object* v___y_2679_ = stack[1].m_obj;
lean_object* v___y_2680_ = stack[2].m_obj;
lean_object* v___y_2681_ = stack[3].m_obj;
lean_object* v___y_2682_ = stack[4].m_obj;
lean_object* v___y_2683_ = stack[5].m_obj;
lean_object* v___y_2684_ = stack[6].m_obj;
lean_object* v_res_2771_;
v_res_2771_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
stack->m_obj
 = v_res_2771_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2780_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2783_ = l_Lean_mkConst(v___x_2782_, v___x_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = lean_box(0);
v___x_2796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2797_ = l_Lean_mkConst(v___x_2796_, v___x_2795_);
return v___x_2797_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2800_, lean_object* v_as_2801_, size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_a_2813_; uint8_t v___x_2817_; 
v___x_2817_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_b_2804_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v_a_2821_; uint8_t v___x_2822_; 
v___x_2819_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2820_ = lean_box(0);
v_a_2821_ = lean_array_uget_borrowed(v_as_2801_, v_i_2803_);
lean_inc(v_a_2821_);
v___x_2822_ = l_Lean_Syntax_isOfKind(v_a_2821_, v___x_2819_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_dec_ref_known(v___x_2823_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2823_;
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = l_Lean_Syntax_getArg(v_a_2821_, v___x_2824_);
v___x_2827_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2826_);
v___x_2828_ = l_Lean_Syntax_isOfKind(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2826_);
v___x_2830_ = l_Lean_Syntax_isOfKind(v___x_2826_, v___x_2829_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
lean_dec(v___x_2826_);
v___x_2831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2831_;
}
}
else
{
lean_object* v___x_2832_; uint8_t v___y_2834_; uint64_t v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___x_2854_; lean_object* v___y_2856_; 
v___x_2832_ = lean_box(0);
v___x_2854_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2824_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2854_);
v___x_2928_ = l_Lean_Syntax_isOfKind(v___x_2854_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
lean_dec(v___x_2854_);
lean_dec(v___x_2826_);
v___x_2929_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref_known(v___x_2929_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2929_;
}
}
else
{
goto v___jp_2922_;
}
}
else
{
goto v___jp_2922_;
}
v___jp_2833_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0);
lean_inc_n(v___y_2836_, 2);
v___x_2845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2845_, 0, v___y_2836_);
lean_ctor_set(v___x_2845_, 1, v___x_2832_);
lean_ctor_set(v___x_2845_, 2, v___x_2844_);
v___x_2846_ = lean_box(0);
v___x_2847_ = 1;
v___x_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___y_2836_);
lean_ctor_set(v___x_2848_, 1, v___x_2832_);
v___x_2849_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2849_, 0, v___x_2845_);
lean_ctor_set(v___x_2849_, 1, v___y_2837_);
lean_ctor_set(v___x_2849_, 2, v___x_2846_);
lean_ctor_set(v___x_2849_, 3, v___x_2848_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*4, v___x_2847_);
v___x_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
v___x_2851_ = l_Lean_addAndCompile(v___x_2850_, v___x_2800_, v___x_2828_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
if (v___y_2834_ == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v___y_2835_, v___y_2836_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_dec_ref_known(v___x_2852_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2852_;
}
}
else
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v___y_2835_, v___y_2836_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref_known(v___x_2853_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2853_;
}
}
}
else
{
lean_dec(v___y_2836_);
return v___x_2851_;
}
}
v___jp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2857_, 0, v___x_2854_);
v___x_2858_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2857_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = l_Lean_Widget_elabWidgetInstanceSpec(v___y_2856_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc_n(v_a_2861_, 2);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2861_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2862_) == 0)
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_unbox(v_a_2859_);
if (v___x_2863_ == 1)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2859_);
v_a_2864_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2865_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2864_, v___y_2808_, v___y_2810_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec_ref_known(v___x_2865_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2865_;
}
}
else
{
lean_object* v_a_2866_; lean_object* v_id_2867_; uint64_t v_javascriptHash_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_a_2866_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2862_, 1);
v_id_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_id_2867_);
v_javascriptHash_2868_ = lean_ctor_get_uint64(v_a_2866_, sizeof(void*)*2);
lean_dec(v_a_2866_);
v___x_2869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2));
v___x_2870_ = l_Lean_Name_append(v_id_2867_, v___x_2869_);
v___x_2871_ = l_Lean_Core_mkFreshUserName(v___x_2870_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2861_, v___y_2808_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; uint8_t v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = l_Lean_Expr_hasMVar(v_a_2874_);
if (v___x_2875_ == 0)
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_unbox(v_a_2859_);
lean_dec(v_a_2859_);
v___y_2834_ = v___x_2876_;
v___y_2835_ = v_javascriptHash_2868_;
v___y_2836_ = v_a_2872_;
v___y_2837_ = v_a_2874_;
v___y_2838_ = v___y_2805_;
v___y_2839_ = v___y_2806_;
v___y_2840_ = v___y_2807_;
v___y_2841_ = v___y_2808_;
v___y_2842_ = v___y_2809_;
v___y_2843_ = v___y_2810_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2874_);
v___x_2878_ = l_Lean_indentExpr(v_a_2874_);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2879_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2880_) == 0)
{
uint8_t v___x_2881_; 
lean_dec_ref_known(v___x_2880_, 1);
v___x_2881_ = lean_unbox(v_a_2859_);
lean_dec(v_a_2859_);
v___y_2834_ = v___x_2881_;
v___y_2835_ = v_javascriptHash_2868_;
v___y_2836_ = v_a_2872_;
v___y_2837_ = v_a_2874_;
v___y_2838_ = v___y_2805_;
v___y_2839_ = v___y_2806_;
v___y_2840_ = v___y_2807_;
v___y_2841_ = v___y_2808_;
v___y_2842_ = v___y_2809_;
v___y_2843_ = v___y_2810_;
goto v___jp_2833_;
}
else
{
lean_dec(v_a_2874_);
lean_dec(v_a_2872_);
lean_dec(v_a_2859_);
return v___x_2880_;
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_a_2872_);
lean_dec(v_a_2859_);
v_a_2882_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2873_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2873_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2859_);
v_a_2890_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2871_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2871_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2859_);
v_a_2898_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2862_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2862_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2859_);
v_a_2906_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2860_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2860_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v___y_2856_);
v_a_2914_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2858_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2858_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
v___jp_2922_:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2825_);
lean_dec(v___x_2826_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2923_);
v___x_2925_ = l_Lean_Syntax_isOfKind(v___x_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v___x_2923_);
lean_dec(v___x_2854_);
v___x_2926_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_dec_ref_known(v___x_2926_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2926_;
}
}
else
{
v___y_2856_ = v___x_2923_;
goto v___jp_2855_;
}
}
else
{
v___y_2856_ = v___x_2923_;
goto v___jp_2855_;
}
}
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2930_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2825_);
lean_dec(v___x_2826_);
v___x_2931_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2930_);
v___x_2932_ = l_Lean_Syntax_isOfKind(v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
lean_dec(v___x_2930_);
v___x_2933_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_dec_ref_known(v___x_2933_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2933_;
}
}
else
{
lean_object* v_toCold_2934_; lean_object* v_ref_2935_; lean_object* v_quotContext_2936_; lean_object* v_currMacroScope_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_toCold_2934_ = lean_ctor_get(v___y_2809_, 0);
v_ref_2935_ = lean_ctor_get(v___y_2809_, 2);
v_quotContext_2936_ = lean_ctor_get(v_toCold_2934_, 8);
v_currMacroScope_2937_ = lean_ctor_get(v_toCold_2934_, 9);
v___x_2938_ = 0;
v___x_2939_ = l_Lean_SourceInfo_fromRef(v_ref_2935_, v___x_2938_);
v___x_2940_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2941_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2942_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2937_);
lean_inc(v_quotContext_2936_);
v___x_2943_ = l_Lean_addMacroScope(v_quotContext_2936_, v___x_2942_, v_currMacroScope_2937_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2939_, 2);
v___x_2945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2939_);
lean_ctor_set(v___x_2945_, 1, v___x_2941_);
lean_ctor_set(v___x_2945_, 2, v___x_2943_);
lean_ctor_set(v___x_2945_, 3, v___x_2944_);
v___x_2946_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2947_ = l_Lean_Syntax_node1(v___x_2939_, v___x_2946_, v___x_2930_);
v___x_2948_ = l_Lean_Syntax_node2(v___x_2939_, v___x_2940_, v___x_2945_, v___x_2947_);
v___x_2949_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2950_ = l_Lean_Elab_Term_elabTerm(v___x_2948_, v___x_2949_, v___x_2800_, v___x_2800_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2951_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; uint64_t v_javascriptHash_2954_; lean_object* v___x_2955_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v_javascriptHash_2954_ = lean_ctor_get_uint64(v_a_2953_, sizeof(void*)*1);
lean_dec(v_a_2953_);
v___x_2955_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2954_, v___y_2808_, v___y_2810_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_dec_ref_known(v___x_2955_, 1);
v_a_2813_ = v___x_2820_;
goto v___jp_2812_;
}
else
{
return v___x_2955_;
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
v_a_2956_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2952_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2952_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2950_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2950_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
}
}
v___jp_2812_:
{
size_t v___x_2814_; size_t v___x_2815_; 
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2803_, v___x_2814_);
v_i_2803_ = v___x_2815_;
v_b_2804_ = v_a_2813_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2800_ = stack[0].m_num;
lean_object* v_as_2801_ = stack[1].m_obj;
size_t v_sz_2802_ = stack[2].m_num;
size_t v_i_2803_ = stack[3].m_num;
lean_object* v_b_2804_ = stack[4].m_obj;
lean_object* v___y_2805_ = stack[5].m_obj;
lean_object* v___y_2806_ = stack[6].m_obj;
lean_object* v___y_2807_ = stack[7].m_obj;
lean_object* v___y_2808_ = stack[8].m_obj;
lean_object* v___y_2809_ = stack[9].m_obj;
lean_object* v___y_2810_ = stack[10].m_obj;
lean_object* v_res_2972_;
v_res_2972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2800_, v_as_2801_, v_sz_2802_, v_i_2803_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
stack->m_obj
 = v_res_2972_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2973_, lean_object* v_as_2974_, lean_object* v_sz_2975_, lean_object* v_i_2976_, lean_object* v_b_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v___x_32555__boxed_2985_; size_t v_sz_boxed_2986_; size_t v_i_boxed_2987_; lean_object* v_res_2988_; 
v___x_32555__boxed_2985_ = lean_unbox(v___x_2973_);
v_sz_boxed_2986_ = lean_unbox_usize(v_sz_2975_);
lean_dec(v_sz_2975_);
v_i_boxed_2987_ = lean_unbox_usize(v_i_2976_);
lean_dec(v_i_2976_);
v_res_2988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_32555__boxed_2985_, v_as_2974_, v_sz_boxed_2986_, v_i_boxed_2987_, v_b_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v_as_2974_);
return v_res_2988_;
}
}
lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2989_, lean_object* v___x_2990_, size_t v_sz_2991_, size_t v___x_2992_, lean_object* v___x_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2989_, v___x_2990_, v_sz_2991_, v___x_2992_, v___x_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v___x_3001_, 0);
lean_dec(v_unused_3009_);
v___x_3003_ = v___x_3001_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_dec(v___x_3001_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_2993_);
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2993_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
return v___x_3001_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2989_ = stack[0].m_num;
lean_object* v___x_2990_ = stack[1].m_obj;
size_t v_sz_2991_ = stack[2].m_num;
size_t v___x_2992_ = stack[3].m_num;
lean_object* v___x_2993_ = stack[4].m_obj;
lean_object* v___y_2994_ = stack[5].m_obj;
lean_object* v___y_2995_ = stack[6].m_obj;
lean_object* v___y_2996_ = stack[7].m_obj;
lean_object* v___y_2997_ = stack[8].m_obj;
lean_object* v___y_2998_ = stack[9].m_obj;
lean_object* v___y_2999_ = stack[10].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_2989_, v___x_2990_, v_sz_2991_, v___x_2992_, v___x_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
stack->m_obj
 = v_res_3010_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v_sz_3013_, lean_object* v___x_3014_, lean_object* v___x_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
uint8_t v___x_33110__boxed_3023_; size_t v_sz_boxed_3024_; size_t v___x_33112__boxed_3025_; lean_object* v_res_3026_; 
v___x_33110__boxed_3023_ = lean_unbox(v___x_3011_);
v_sz_boxed_3024_ = lean_unbox_usize(v_sz_3013_);
lean_dec(v_sz_3013_);
v___x_33112__boxed_3025_ = lean_unbox_usize(v___x_3014_);
lean_dec(v___x_3014_);
v_res_3026_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_33110__boxed_3023_, v___x_3012_, v_sz_boxed_3024_, v___x_33112__boxed_3025_, v___x_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec_ref(v___x_3012_);
return v_res_3026_;
}
}
lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_3029_);
v___x_3034_ = l_Lean_Syntax_isOfKind(v_x_3029_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
lean_dec(v_x_3029_);
v___x_3035_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_ws_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; size_t v_sz_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___f_3045_; lean_object* v___x_3046_; 
v___x_3036_ = lean_unsigned_to_nat(2u);
v___x_3037_ = l_Lean_Syntax_getArg(v_x_3029_, v___x_3036_);
lean_dec(v_x_3029_);
v_ws_3038_ = l_Lean_Syntax_getArgs(v___x_3037_);
lean_dec(v___x_3037_);
v___x_3039_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_3038_);
lean_dec_ref(v_ws_3038_);
v___x_3040_ = lean_box(0);
v_sz_3041_ = lean_array_size(v___x_3039_);
v___x_3042_ = lean_box(v___x_3034_);
v___x_3043_ = lean_box_usize(v_sz_3041_);
v___x_3044_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_3045_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3045_, 0, v___x_3042_);
lean_closure_set(v___f_3045_, 1, v___x_3039_);
lean_closure_set(v___f_3045_, 2, v___x_3043_);
lean_closure_set(v___f_3045_, 3, v___x_3044_);
lean_closure_set(v___f_3045_, 4, v___x_3040_);
v___x_3046_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3045_, v_a_3030_, v_a_3031_);
return v___x_3046_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_elabShowPanelWidgetsCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3029_ = stack[0].m_obj;
lean_object* v_a_3030_ = stack[1].m_obj;
lean_object* v_a_3031_ = stack[2].m_obj;
lean_object* v_res_3047_;
v_res_3047_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_3029_, v_a_3030_, v_a_3031_);
stack->m_obj
 = v_res_3047_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_3053_, lean_object* v_x_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_3054_, v___y_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_3058_, v_x_3059_, v___y_3060_, v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v_x_3059_);
return v_res_3062_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_3063_, lean_object* v_ref_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_3064_);
return v___x_3072_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3064_ = stack[1].m_obj;
lean_object* v___y_3065_ = stack[2].m_obj;
lean_object* v___y_3066_ = stack[3].m_obj;
lean_object* v___y_3067_ = stack[4].m_obj;
lean_object* v___y_3068_ = stack[5].m_obj;
lean_object* v___y_3069_ = stack[6].m_obj;
lean_object* v___y_3070_ = stack[7].m_obj;
lean_object* v_res_3073_;
v_res_3073_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_box(0), v_ref_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
stack->m_obj
 = v_res_3073_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3074_, lean_object* v_ref_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3074_, v_ref_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3083_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3084_, lean_object* v_x_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3085_ = stack[1].m_obj;
lean_object* v___y_3086_ = stack[2].m_obj;
lean_object* v___y_3087_ = stack[3].m_obj;
lean_object* v___y_3088_ = stack[4].m_obj;
lean_object* v___y_3089_ = stack[5].m_obj;
lean_object* v___y_3090_ = stack[6].m_obj;
lean_object* v___y_3091_ = stack[7].m_obj;
lean_object* v_res_3094_;
v_res_3094_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_box(0), v_x_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
stack->m_obj
 = v_res_3094_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3095_, lean_object* v_x_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3095_, v_x_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3104_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3105_, v___y_3109_, v___y_3111_);
return v___x_3113_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_wi_3105_ = stack[0].m_obj;
lean_object* v___y_3106_ = stack[1].m_obj;
lean_object* v___y_3107_ = stack[2].m_obj;
lean_object* v___y_3108_ = stack[3].m_obj;
lean_object* v___y_3109_ = stack[4].m_obj;
lean_object* v___y_3110_ = stack[5].m_obj;
lean_object* v___y_3111_ = stack[6].m_obj;
lean_object* v_res_3114_;
v_res_3114_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
stack->m_obj
 = v_res_3114_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
return v_res_3123_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object* v_00_u03b1_3124_, lean_object* v_00_u03b2_3125_, lean_object* v_00_u03c3_3126_, lean_object* v_ext_3127_, lean_object* v_b_3128_, uint8_t v_kind_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_3127_, v_b_3128_, v_kind_3129_, v___y_3133_, v___y_3134_, v___y_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_3127_ = stack[3].m_obj;
lean_object* v_b_3128_ = stack[4].m_obj;
uint8_t v_kind_3129_ = stack[5].m_num;
lean_object* v___y_3130_ = stack[6].m_obj;
lean_object* v___y_3131_ = stack[7].m_obj;
lean_object* v___y_3132_ = stack[8].m_obj;
lean_object* v___y_3133_ = stack[9].m_obj;
lean_object* v___y_3134_ = stack[10].m_obj;
lean_object* v___y_3135_ = stack[11].m_obj;
lean_object* v_res_3138_;
v_res_3138_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_box(0), lean_box(0), lean_box(0), v_ext_3127_, v_b_3128_, v_kind_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
stack->m_obj
 = v_res_3138_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object* v_00_u03b1_3139_, lean_object* v_00_u03b2_3140_, lean_object* v_00_u03c3_3141_, lean_object* v_ext_3142_, lean_object* v_b_3143_, lean_object* v_kind_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
uint8_t v_kind_boxed_3152_; lean_object* v_res_3153_; 
v_kind_boxed_3152_ = lean_unbox(v_kind_3144_);
v_res_3153_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_3139_, v_00_u03b2_3140_, v_00_u03c3_3141_, v_ext_3142_, v_b_3143_, v_kind_boxed_3152_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
return v_res_3153_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3154_, lean_object* v_msg_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3155_ = stack[1].m_obj;
lean_object* v___y_3156_ = stack[2].m_obj;
lean_object* v___y_3157_ = stack[3].m_obj;
lean_object* v___y_3158_ = stack[4].m_obj;
lean_object* v___y_3159_ = stack[5].m_obj;
lean_object* v___y_3160_ = stack[6].m_obj;
lean_object* v___y_3161_ = stack[7].m_obj;
lean_object* v_res_3164_;
v_res_3164_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_box(0), v_msg_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
stack->m_obj
 = v_res_3164_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3165_, lean_object* v_msg_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3165_, v_msg_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3174_;
}
}
lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3175_, v___y_3179_, v___y_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT void l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_3175_ = stack[0].m_num;
lean_object* v___y_3176_ = stack[1].m_obj;
lean_object* v___y_3177_ = stack[2].m_obj;
lean_object* v___y_3178_ = stack[3].m_obj;
lean_object* v___y_3179_ = stack[4].m_obj;
lean_object* v___y_3180_ = stack[5].m_obj;
lean_object* v___y_3181_ = stack[6].m_obj;
lean_object* v_res_3184_;
v_res_3184_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
stack->m_obj
 = v_res_3184_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
uint64_t v_h_boxed_3193_; lean_object* v_res_3194_; 
v_h_boxed_3193_ = lean_unbox_uint64(v_h_3185_);
lean_dec_ref(v_h_3185_);
v_res_3194_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3193_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
return v_res_3194_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3195_, lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3195_, v_msg_3196_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3195_ = stack[0].m_obj;
lean_object* v_msg_3196_ = stack[1].m_obj;
lean_object* v___y_3197_ = stack[2].m_obj;
lean_object* v___y_3198_ = stack[3].m_obj;
lean_object* v___y_3199_ = stack[4].m_obj;
lean_object* v___y_3200_ = stack[5].m_obj;
lean_object* v___y_3201_ = stack[6].m_obj;
lean_object* v___y_3202_ = stack[7].m_obj;
lean_object* v_res_3205_;
v_res_3205_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3195_, v_msg_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
stack->m_obj
 = v_res_3205_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3206_, lean_object* v_msg_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3206_, v_msg_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3215_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3216_, lean_object* v_as_x27_3217_, lean_object* v_b_3218_, lean_object* v_a_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3217_, v_b_3218_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v___x_3227_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3216_ = stack[0].m_obj;
lean_object* v_as_x27_3217_ = stack[1].m_obj;
lean_object* v_b_3218_ = stack[2].m_obj;
lean_object* v___y_3220_ = stack[4].m_obj;
lean_object* v___y_3221_ = stack[5].m_obj;
lean_object* v___y_3222_ = stack[6].m_obj;
lean_object* v___y_3223_ = stack[7].m_obj;
lean_object* v___y_3224_ = stack[8].m_obj;
lean_object* v___y_3225_ = stack[9].m_obj;
lean_object* v_res_3228_;
v_res_3228_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3216_, v_as_x27_3217_, v_b_3218_, lean_box(0), v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
stack->m_obj
 = v_res_3228_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3229_, lean_object* v_as_x27_3230_, lean_object* v_b_3231_, lean_object* v_a_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3229_, v_as_x27_3230_, v_b_3231_, v_a_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v_as_x27_3230_);
lean_dec(v_as_3229_);
return v_res_3240_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3241_, lean_object* v_ref_3242_, lean_object* v_msg_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3242_, v_msg_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3242_ = stack[1].m_obj;
lean_object* v_msg_3243_ = stack[2].m_obj;
lean_object* v___y_3244_ = stack[3].m_obj;
lean_object* v___y_3245_ = stack[4].m_obj;
lean_object* v___y_3246_ = stack[5].m_obj;
lean_object* v___y_3247_ = stack[6].m_obj;
lean_object* v___y_3248_ = stack[7].m_obj;
lean_object* v___y_3249_ = stack[8].m_obj;
lean_object* v_res_3252_;
v_res_3252_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_box(0), v_ref_3242_, v_msg_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
stack->m_obj
 = v_res_3252_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3253_, lean_object* v_ref_3254_, lean_object* v_msg_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3253_, v_ref_3254_, v_msg_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v_ref_3254_);
return v_res_3263_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3264_, lean_object* v_t_3265_, uint64_t v_k_3266_, lean_object* v_fallback_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3265_, v_k_3266_, v_fallback_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3265_ = stack[1].m_obj;
uint64_t v_k_3266_ = stack[2].m_num;
lean_object* v_fallback_3267_ = stack[3].m_obj;
lean_object* v_res_3269_;
v_res_3269_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_box(0), v_t_3265_, v_k_3266_, v_fallback_3267_);
stack->m_obj
 = v_res_3269_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3270_, lean_object* v_t_3271_, lean_object* v_k_3272_, lean_object* v_fallback_3273_){
_start:
{
uint64_t v_k_boxed_3274_; lean_object* v_res_3275_; 
v_k_boxed_3274_ = lean_unbox_uint64(v_k_3272_);
lean_dec_ref(v_k_3272_);
v_res_3275_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3270_, v_t_3271_, v_k_boxed_3274_, v_fallback_3273_);
lean_dec(v_fallback_3273_);
lean_dec(v_t_3271_);
return v_res_3275_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3276_, uint64_t v_k_3277_, lean_object* v_v_3278_, lean_object* v_t_3279_, lean_object* v_hl_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3277_, v_v_3278_, v_t_3279_);
return v___x_3281_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_3277_ = stack[1].m_num;
lean_object* v_v_3278_ = stack[2].m_obj;
lean_object* v_t_3279_ = stack[3].m_obj;
lean_object* v_res_3282_;
v_res_3282_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_box(0), v_k_3277_, v_v_3278_, v_t_3279_, lean_box(0));
stack->m_obj
 = v_res_3282_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3283_, lean_object* v_k_3284_, lean_object* v_v_3285_, lean_object* v_t_3286_, lean_object* v_hl_3287_){
_start:
{
uint64_t v_k_boxed_3288_; lean_object* v_res_3289_; 
v_k_boxed_3288_ = lean_unbox_uint64(v_k_3284_);
lean_dec_ref(v_k_3284_);
v_res_3289_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3283_, v_k_boxed_3288_, v_v_3285_, v_t_3286_, v_hl_3287_);
return v_res_3289_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_3290_, lean_object* v_macroStack_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_3290_, v_macroStack_3291_, v___y_3296_);
return v___x_3299_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3290_ = stack[0].m_obj;
lean_object* v_macroStack_3291_ = stack[1].m_obj;
lean_object* v___y_3292_ = stack[2].m_obj;
lean_object* v___y_3293_ = stack[3].m_obj;
lean_object* v___y_3294_ = stack[4].m_obj;
lean_object* v___y_3295_ = stack[5].m_obj;
lean_object* v___y_3296_ = stack[6].m_obj;
lean_object* v___y_3297_ = stack[7].m_obj;
lean_object* v_res_3300_;
v_res_3300_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3290_, v_macroStack_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
stack->m_obj
 = v_res_3300_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_3301_, lean_object* v_macroStack_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3301_, v_macroStack_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
return v_res_3310_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object* v_00_u03b2_3311_, uint64_t v_k_3312_, lean_object* v_t_3313_, lean_object* v_h_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3312_, v_t_3313_);
return v___x_3315_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_3312_ = stack[1].m_num;
lean_object* v_t_3313_ = stack[2].m_obj;
lean_object* v_res_3316_;
v_res_3316_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_box(0), v_k_3312_, v_t_3313_, lean_box(0));
stack->m_obj
 = v_res_3316_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_k_3318_, lean_object* v_t_3319_, lean_object* v_h_3320_){
_start:
{
uint64_t v_k_boxed_3321_; lean_object* v_res_3322_; 
v_k_boxed_3321_ = lean_unbox_uint64(v_k_3318_);
lean_dec_ref(v_k_3318_);
v_res_3322_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_3317_, v_k_boxed_3321_, v_t_3319_, v_h_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3323_, lean_object* v_m_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3324_, v_a_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_m_3328_, lean_object* v_a_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3327_, v_m_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_m_3328_);
return v_res_3330_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object* v_00_u03b2_3331_, lean_object* v_x_3332_, lean_object* v_x_3333_){
_start:
{
uint8_t v___x_3334_; 
v___x_3334_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_3332_, v_x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3332_ = stack[1].m_obj;
lean_object* v_x_3333_ = stack[2].m_obj;
uint8_t v_res_3335_;
v_res_3335_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_box(0), v_x_3332_, v_x_3333_);
stack->m_num = v_res_3335_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object* v_00_u03b2_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_3336_, v_x_3337_, v_x_3338_);
lean_dec_ref(v_x_3338_);
lean_dec_ref(v_x_3337_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object* v_00_u03b2_3341_, lean_object* v_a_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_3342_, v_x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object* v_00_u03b2_3345_, lean_object* v_a_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_3345_, v_a_3346_, v_x_3347_);
lean_dec(v_x_3347_);
lean_dec(v_a_3346_);
return v_res_3348_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object* v_00_u03b2_3349_, lean_object* v_x_3350_, size_t v_x_3351_, lean_object* v_x_3352_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_3350_, v_x_3351_, v_x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3350_ = stack[1].m_obj;
size_t v_x_3351_ = stack[2].m_num;
lean_object* v_x_3352_ = stack[3].m_obj;
uint8_t v_res_3354_;
v_res_3354_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_box(0), v_x_3350_, v_x_3351_, v_x_3352_);
stack->m_num = v_res_3354_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object* v_00_u03b2_3355_, lean_object* v_x_3356_, lean_object* v_x_3357_, lean_object* v_x_3358_){
_start:
{
size_t v_x_33694__boxed_3359_; uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_x_33694__boxed_3359_ = lean_unbox_usize(v_x_3357_);
lean_dec(v_x_3357_);
v_res_3360_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_3355_, v_x_3356_, v_x_33694__boxed_3359_, v_x_3358_);
lean_dec_ref(v_x_3358_);
lean_dec_ref(v_x_3356_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object* v_00_u03b2_3362_, lean_object* v_keys_3363_, lean_object* v_vals_3364_, lean_object* v_heq_3365_, lean_object* v_i_3366_, lean_object* v_k_3367_){
_start:
{
uint8_t v___x_3368_; 
v___x_3368_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_3363_, v_i_3366_, v_k_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3363_ = stack[1].m_obj;
lean_object* v_vals_3364_ = stack[2].m_obj;
lean_object* v_i_3366_ = stack[4].m_obj;
lean_object* v_k_3367_ = stack[5].m_obj;
uint8_t v_res_3369_;
v_res_3369_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_box(0), v_keys_3363_, v_vals_3364_, lean_box(0), v_i_3366_, v_k_3367_);
stack->m_num = v_res_3369_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object* v_00_u03b2_3370_, lean_object* v_keys_3371_, lean_object* v_vals_3372_, lean_object* v_heq_3373_, lean_object* v_i_3374_, lean_object* v_k_3375_){
_start:
{
uint8_t v_res_3376_; lean_object* v_r_3377_; 
v_res_3376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_3370_, v_keys_3371_, v_vals_3372_, v_heq_3373_, v_i_3374_, v_k_3375_);
lean_dec_ref(v_k_3375_);
lean_dec_ref(v_vals_3372_);
lean_dec_ref(v_keys_3371_);
v_r_3377_ = lean_box(v_res_3376_);
return v_r_3377_;
}
}
lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3395_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v___x_3406_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3405_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; uint64_t v_javascriptHash_3408_; lean_object* v_props_3409_; lean_object* v___x_3410_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v_javascriptHash_3408_ = lean_ctor_get_uint64(v_a_3407_, sizeof(void*)*2);
v_props_3409_ = lean_ctor_get(v_a_3407_, 1);
lean_inc_ref(v_props_3409_);
lean_dec(v_a_3407_);
v___x_3410_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3408_, v_props_3409_, v_x_3396_, v___y_3401_, v___y_3402_);
return v___x_3410_;
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_x_3396_);
v_a_3411_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3406_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3406_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_x_3396_);
v_a_3419_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3404_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3404_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_elabWidgetCmd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3395_ = stack[0].m_obj;
lean_object* v_x_3396_ = stack[1].m_obj;
lean_object* v___y_3397_ = stack[2].m_obj;
lean_object* v___y_3398_ = stack[3].m_obj;
lean_object* v___y_3399_ = stack[4].m_obj;
lean_object* v___y_3400_ = stack[5].m_obj;
lean_object* v___y_3401_ = stack[6].m_obj;
lean_object* v___y_3402_ = stack[7].m_obj;
lean_object* v_res_3427_;
v_res_3427_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3395_, v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
stack->m_obj
 = v_res_3427_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3428_, v_x_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3437_;
}
}
lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3438_);
v___x_3443_ = l_Lean_Syntax_isOfKind(v_x_3438_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_dec(v_x_3438_);
v___x_3444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3444_;
}
else
{
lean_object* v___x_3445_; lean_object* v_s_3446_; lean_object* v___f_3447_; lean_object* v___x_3448_; 
v___x_3445_ = lean_unsigned_to_nat(1u);
v_s_3446_ = l_Lean_Syntax_getArg(v_x_3438_, v___x_3445_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3447_, 0, v_s_3446_);
lean_closure_set(v___f_3447_, 1, v_x_3438_);
v___x_3448_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3447_, v_a_3439_, v_a_3440_);
return v___x_3448_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_elabWidgetCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3438_ = stack[0].m_obj;
lean_object* v_a_3439_ = stack[1].m_obj;
lean_object* v_a_3440_ = stack[2].m_obj;
lean_object* v_res_3449_;
v_res_3449_ = l_Lean_Widget_elabWidgetCmd(v_x_3438_, v_a_3439_, v_a_3440_);
stack->m_obj
 = v_res_3449_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Widget_elabWidgetCmd(v_x_3450_, v_a_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3454_;
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
