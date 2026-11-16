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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 220, 71, 116, 84, 119, 12, 45)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_611_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg(){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__1);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___boxed(lean_object* v___dummy_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg();
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(uint64_t v_k_618_, lean_object* v_t_619_){
_start:
{
if (lean_obj_tag(v_t_619_) == 0)
{
lean_object* v_k_620_; lean_object* v_v_621_; lean_object* v_l_622_; lean_object* v_r_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_1280_; 
v_k_620_ = lean_ctor_get(v_t_619_, 1);
v_v_621_ = lean_ctor_get(v_t_619_, 2);
v_l_622_ = lean_ctor_get(v_t_619_, 3);
v_r_623_ = lean_ctor_get(v_t_619_, 4);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_t_619_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v_t_619_, 0);
lean_dec(v_unused_1281_);
v___x_625_ = v_t_619_;
v_isShared_626_ = v_isSharedCheck_1280_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_r_623_);
lean_inc(v_l_622_);
lean_inc(v_v_621_);
lean_inc(v_k_620_);
lean_dec(v_t_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_1280_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint64_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_unbox_uint64(v_k_620_);
v___x_628_ = lean_uint64_dec_lt(v_k_618_, v___x_627_);
if (v___x_628_ == 0)
{
uint64_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_unbox_uint64(v_k_620_);
v___x_630_ = lean_uint64_dec_eq(v_k_618_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v_impl_631_; lean_object* v___x_632_; 
v_impl_631_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_618_, v_r_623_);
v___x_632_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_631_) == 0)
{
if (lean_obj_tag(v_l_622_) == 0)
{
lean_object* v_size_633_; lean_object* v_size_634_; lean_object* v_k_635_; lean_object* v_v_636_; lean_object* v_l_637_; lean_object* v_r_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_size_633_ = lean_ctor_get(v_impl_631_, 0);
v_size_634_ = lean_ctor_get(v_l_622_, 0);
v_k_635_ = lean_ctor_get(v_l_622_, 1);
v_v_636_ = lean_ctor_get(v_l_622_, 2);
v_l_637_ = lean_ctor_get(v_l_622_, 3);
v_r_638_ = lean_ctor_get(v_l_622_, 4);
lean_inc(v_r_638_);
v___x_639_ = lean_unsigned_to_nat(3u);
v___x_640_ = lean_nat_mul(v___x_639_, v_size_633_);
v___x_641_ = lean_nat_dec_lt(v___x_640_, v_size_634_);
lean_dec(v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
lean_dec(v_r_638_);
v___x_642_ = lean_nat_add(v___x_632_, v_size_634_);
v___x_643_ = lean_nat_add(v___x_642_, v_size_633_);
lean_dec(v___x_642_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_impl_631_);
lean_ctor_set(v___x_625_, 0, v___x_643_);
v___x_645_ = v___x_625_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v_impl_631_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_712_; 
lean_inc(v_l_637_);
lean_inc(v_v_636_);
lean_inc(v_k_635_);
lean_inc(v_size_634_);
v_isSharedCheck_712_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; 
v_unused_713_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_l_622_, 2);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_l_622_, 1);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_717_);
v___x_648_ = v_l_622_;
v_isShared_649_ = v_isSharedCheck_712_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_l_622_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_712_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_size_650_; lean_object* v_size_651_; lean_object* v_k_652_; lean_object* v_v_653_; lean_object* v_l_654_; lean_object* v_r_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_size_650_ = lean_ctor_get(v_l_637_, 0);
v_size_651_ = lean_ctor_get(v_r_638_, 0);
v_k_652_ = lean_ctor_get(v_r_638_, 1);
v_v_653_ = lean_ctor_get(v_r_638_, 2);
v_l_654_ = lean_ctor_get(v_r_638_, 3);
v_r_655_ = lean_ctor_get(v_r_638_, 4);
v___x_656_ = lean_unsigned_to_nat(2u);
v___x_657_ = lean_nat_mul(v___x_656_, v_size_650_);
v___x_658_ = lean_nat_dec_lt(v_size_651_, v___x_657_);
lean_dec(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_687_; 
lean_inc(v_r_655_);
lean_inc(v_l_654_);
lean_inc(v_v_653_);
lean_inc(v_k_652_);
v_isSharedCheck_687_ = !lean_is_exclusive(v_r_638_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; 
v_unused_688_ = lean_ctor_get(v_r_638_, 4);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_r_638_, 3);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_r_638_, 2);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_r_638_, 1);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_r_638_, 0);
lean_dec(v_unused_692_);
v___x_660_ = v_r_638_;
v_isShared_661_ = v_isSharedCheck_687_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_r_638_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_687_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___x_675_; lean_object* v___y_677_; 
v___x_662_ = lean_nat_add(v___x_632_, v_size_634_);
lean_dec(v_size_634_);
v___x_663_ = lean_nat_add(v___x_662_, v_size_633_);
lean_dec(v___x_662_);
v___x_675_ = lean_nat_add(v___x_632_, v_size_650_);
if (lean_obj_tag(v_l_654_) == 0)
{
lean_object* v_size_685_; 
v_size_685_ = lean_ctor_get(v_l_654_, 0);
lean_inc(v_size_685_);
v___y_677_ = v_size_685_;
goto v___jp_676_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___y_677_ = v___x_686_;
goto v___jp_676_;
}
v___jp_664_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = lean_nat_add(v___y_665_, v___y_667_);
lean_dec(v___y_667_);
lean_dec(v___y_665_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 4, v_impl_631_);
lean_ctor_set(v___x_660_, 3, v_r_655_);
lean_ctor_set(v___x_660_, 2, v_v_621_);
lean_ctor_set(v___x_660_, 1, v_k_620_);
lean_ctor_set(v___x_660_, 0, v___x_668_);
v___x_670_ = v___x_660_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_r_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_impl_631_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 4, v___x_670_);
lean_ctor_set(v___x_648_, 3, v___y_666_);
lean_ctor_set(v___x_648_, 2, v_v_653_);
lean_ctor_set(v___x_648_, 1, v_k_652_);
lean_ctor_set(v___x_648_, 0, v___x_663_);
v___x_672_ = v___x_648_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v___y_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_nat_add(v___x_675_, v___y_677_);
lean_dec(v___y_677_);
lean_dec(v___x_675_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_l_654_);
lean_ctor_set(v___x_625_, 3, v_l_637_);
lean_ctor_set(v___x_625_, 2, v_v_636_);
lean_ctor_set(v___x_625_, 1, v_k_635_);
lean_ctor_set(v___x_625_, 0, v___x_678_);
v___x_680_ = v___x_625_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_l_654_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_nat_add(v___x_632_, v_size_633_);
if (lean_obj_tag(v_r_655_) == 0)
{
lean_object* v_size_682_; 
v_size_682_ = lean_ctor_get(v_r_655_, 0);
lean_inc(v_size_682_);
v___y_665_ = v___x_681_;
v___y_666_ = v___x_680_;
v___y_667_ = v_size_682_;
goto v___jp_664_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___y_665_ = v___x_681_;
v___y_666_ = v___x_680_;
v___y_667_ = v___x_683_;
goto v___jp_664_;
}
}
}
}
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_del_object(v___x_625_);
v___x_693_ = lean_nat_add(v___x_632_, v_size_634_);
lean_dec(v_size_634_);
v___x_694_ = lean_nat_add(v___x_693_, v_size_633_);
lean_dec(v___x_693_);
v___x_695_ = lean_nat_add(v___x_632_, v_size_633_);
v___x_696_ = lean_nat_add(v___x_695_, v_size_651_);
lean_dec(v___x_695_);
lean_inc_ref(v_impl_631_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 4, v_impl_631_);
lean_ctor_set(v___x_648_, 3, v_r_638_);
lean_ctor_set(v___x_648_, 2, v_v_621_);
lean_ctor_set(v___x_648_, 1, v_k_620_);
lean_ctor_set(v___x_648_, 0, v___x_696_);
v___x_698_ = v___x_648_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_r_638_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_impl_631_);
v___x_698_ = v_reuseFailAlloc_711_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_isSharedCheck_705_ = !lean_is_exclusive(v_impl_631_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_706_ = lean_ctor_get(v_impl_631_, 4);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_impl_631_, 3);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_impl_631_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_impl_631_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_impl_631_, 0);
lean_dec(v_unused_710_);
v___x_700_ = v_impl_631_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_impl_631_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 4, v___x_698_);
lean_ctor_set(v___x_700_, 3, v_l_637_);
lean_ctor_set(v___x_700_, 2, v_v_636_);
lean_ctor_set(v___x_700_, 1, v_k_635_);
lean_ctor_set(v___x_700_, 0, v___x_694_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v___x_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v_size_718_ = lean_ctor_get(v_impl_631_, 0);
v___x_719_ = lean_nat_add(v___x_632_, v_size_718_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_impl_631_);
lean_ctor_set(v___x_625_, 0, v___x_719_);
v___x_721_ = v___x_625_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_impl_631_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
if (lean_obj_tag(v_l_622_) == 0)
{
lean_object* v_l_723_; 
v_l_723_ = lean_ctor_get(v_l_622_, 3);
if (lean_obj_tag(v_l_723_) == 0)
{
lean_object* v_r_724_; 
lean_inc_ref(v_l_723_);
v_r_724_ = lean_ctor_get(v_l_622_, 4);
lean_inc(v_r_724_);
if (lean_obj_tag(v_r_724_) == 0)
{
lean_object* v_size_725_; lean_object* v_k_726_; lean_object* v_v_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_740_; 
v_size_725_ = lean_ctor_get(v_l_622_, 0);
v_k_726_ = lean_ctor_get(v_l_622_, 1);
v_v_727_ = lean_ctor_get(v_l_622_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; lean_object* v_unused_742_; 
v_unused_741_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_742_);
v___x_729_ = v_l_622_;
v_isShared_730_ = v_isSharedCheck_740_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_v_727_);
lean_inc(v_k_726_);
lean_inc(v_size_725_);
lean_dec(v_l_622_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_740_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_size_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v_size_731_ = lean_ctor_get(v_r_724_, 0);
v___x_732_ = lean_nat_add(v___x_632_, v_size_725_);
lean_dec(v_size_725_);
v___x_733_ = lean_nat_add(v___x_632_, v_size_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 4, v_impl_631_);
lean_ctor_set(v___x_729_, 3, v_r_724_);
lean_ctor_set(v___x_729_, 2, v_v_621_);
lean_ctor_set(v___x_729_, 1, v_k_620_);
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_r_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_impl_631_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_735_);
lean_ctor_set(v___x_625_, 3, v_l_723_);
lean_ctor_set(v___x_625_, 2, v_v_727_);
lean_ctor_set(v___x_625_, 1, v_k_726_);
lean_ctor_set(v___x_625_, 0, v___x_732_);
v___x_737_ = v___x_625_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_k_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_v_727_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_k_743_; lean_object* v_v_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v_k_743_ = lean_ctor_get(v_l_622_, 1);
v_v_744_ = lean_ctor_get(v_l_622_, 2);
v_isSharedCheck_755_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; 
v_unused_756_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_758_);
v___x_746_ = v_l_622_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_v_744_);
lean_inc(v_k_743_);
lean_dec(v_l_622_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(3u);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 3, v_r_724_);
lean_ctor_set(v___x_746_, 2, v_v_621_);
lean_ctor_set(v___x_746_, 1, v_k_620_);
lean_ctor_set(v___x_746_, 0, v___x_632_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_r_724_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_r_724_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_750_);
lean_ctor_set(v___x_625_, 3, v_l_723_);
lean_ctor_set(v___x_625_, 2, v_v_744_);
lean_ctor_set(v___x_625_, 1, v_k_743_);
lean_ctor_set(v___x_625_, 0, v___x_748_);
v___x_752_ = v___x_625_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_743_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_744_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v_r_759_; 
v_r_759_ = lean_ctor_get(v_l_622_, 4);
lean_inc(v_r_759_);
if (lean_obj_tag(v_r_759_) == 0)
{
lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_784_; 
lean_inc(v_l_723_);
v_k_760_ = lean_ctor_get(v_l_622_, 1);
v_v_761_ = lean_ctor_get(v_l_622_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_785_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_787_);
v___x_763_ = v_l_622_;
v_isShared_764_ = v_isSharedCheck_784_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_v_761_);
lean_inc(v_k_760_);
lean_dec(v_l_622_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_784_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_k_765_; lean_object* v_v_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_780_; 
v_k_765_ = lean_ctor_get(v_r_759_, 1);
v_v_766_ = lean_ctor_get(v_r_759_, 2);
v_isSharedCheck_780_ = !lean_is_exclusive(v_r_759_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; 
v_unused_781_ = lean_ctor_get(v_r_759_, 4);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_759_, 3);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_759_, 0);
lean_dec(v_unused_783_);
v___x_768_ = v_r_759_;
v_isShared_769_ = v_isSharedCheck_780_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_v_766_);
lean_inc(v_k_765_);
lean_dec(v_r_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_780_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(3u);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 4, v_l_723_);
lean_ctor_set(v___x_768_, 3, v_l_723_);
lean_ctor_set(v___x_768_, 2, v_v_761_);
lean_ctor_set(v___x_768_, 1, v_k_760_);
lean_ctor_set(v___x_768_, 0, v___x_632_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_l_723_);
v___x_772_ = v_reuseFailAlloc_779_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_l_723_);
lean_ctor_set(v___x_763_, 2, v_v_621_);
lean_ctor_set(v___x_763_, 1, v_k_620_);
lean_ctor_set(v___x_763_, 0, v___x_632_);
v___x_774_ = v___x_763_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_l_723_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_774_);
lean_ctor_set(v___x_625_, 3, v___x_772_);
lean_ctor_set(v___x_625_, 2, v_v_766_);
lean_ctor_set(v___x_625_, 1, v_k_765_);
lean_ctor_set(v___x_625_, 0, v___x_770_);
v___x_776_ = v___x_625_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_unsigned_to_nat(2u);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_r_759_);
lean_ctor_set(v___x_625_, 0, v___x_788_);
v___x_790_ = v___x_625_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_r_759_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v___x_793_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_l_622_);
lean_ctor_set(v___x_625_, 0, v___x_632_);
v___x_793_ = v___x_625_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_l_622_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_del_object(v___x_625_);
lean_dec(v_v_621_);
lean_dec(v_k_620_);
if (lean_obj_tag(v_l_622_) == 0)
{
if (lean_obj_tag(v_r_623_) == 0)
{
lean_object* v_size_795_; lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v_l_798_; lean_object* v_r_799_; lean_object* v_size_800_; lean_object* v_k_801_; lean_object* v_v_802_; lean_object* v_l_803_; lean_object* v_r_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_size_795_ = lean_ctor_get(v_l_622_, 0);
v_k_796_ = lean_ctor_get(v_l_622_, 1);
v_v_797_ = lean_ctor_get(v_l_622_, 2);
v_l_798_ = lean_ctor_get(v_l_622_, 3);
v_r_799_ = lean_ctor_get(v_l_622_, 4);
lean_inc(v_r_799_);
v_size_800_ = lean_ctor_get(v_r_623_, 0);
v_k_801_ = lean_ctor_get(v_r_623_, 1);
v_v_802_ = lean_ctor_get(v_r_623_, 2);
v_l_803_ = lean_ctor_get(v_r_623_, 3);
lean_inc(v_l_803_);
v_r_804_ = lean_ctor_get(v_r_623_, 4);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_dec_lt(v_size_795_, v_size_800_);
if (v___x_806_ == 0)
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_942_; 
lean_inc(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; 
v_unused_943_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_622_, 2);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_l_622_, 1);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_947_);
v___x_808_ = v_l_622_;
v_isShared_809_ = v_isSharedCheck_942_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_l_622_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_942_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v_tree_811_; 
v___x_810_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_796_, v_v_797_, v_l_798_, v_r_799_);
v_tree_811_ = lean_ctor_get(v___x_810_, 2);
if (lean_obj_tag(v_tree_811_) == 0)
{
lean_object* v_k_812_; lean_object* v_v_813_; lean_object* v_size_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
lean_inc_ref(v_tree_811_);
v_k_812_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_k_812_);
v_v_813_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_v_813_);
lean_dec_ref(v___x_810_);
v_size_814_ = lean_ctor_get(v_tree_811_, 0);
v___x_815_ = lean_unsigned_to_nat(3u);
v___x_816_ = lean_nat_mul(v___x_815_, v_size_814_);
v___x_817_ = lean_nat_dec_lt(v___x_816_, v_size_800_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v_l_803_);
v___x_818_ = lean_nat_add(v___x_805_, v_size_814_);
v___x_819_ = lean_nat_add(v___x_818_, v_size_800_);
lean_dec(v___x_818_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_r_623_);
lean_ctor_set(v___x_808_, 3, v_tree_811_);
lean_ctor_set(v___x_808_, 2, v_v_813_);
lean_ctor_set(v___x_808_, 1, v_k_812_);
lean_ctor_set(v___x_808_, 0, v___x_819_);
v___x_821_ = v___x_808_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_tree_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_r_623_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_877_; 
lean_inc(v_r_804_);
lean_inc(v_v_802_);
lean_inc(v_k_801_);
lean_inc(v_size_800_);
v_isSharedCheck_877_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; lean_object* v_unused_879_; lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; 
v_unused_878_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_r_623_, 2);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_r_623_, 1);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_r_623_, 0);
lean_dec(v_unused_882_);
v___x_824_ = v_r_623_;
v_isShared_825_ = v_isSharedCheck_877_;
goto v_resetjp_823_;
}
else
{
lean_dec(v_r_623_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_877_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_size_826_; lean_object* v_k_827_; lean_object* v_v_828_; lean_object* v_l_829_; lean_object* v_r_830_; lean_object* v_size_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_size_826_ = lean_ctor_get(v_l_803_, 0);
v_k_827_ = lean_ctor_get(v_l_803_, 1);
v_v_828_ = lean_ctor_get(v_l_803_, 2);
v_l_829_ = lean_ctor_get(v_l_803_, 3);
v_r_830_ = lean_ctor_get(v_l_803_, 4);
v_size_831_ = lean_ctor_get(v_r_804_, 0);
v___x_832_ = lean_unsigned_to_nat(2u);
v___x_833_ = lean_nat_mul(v___x_832_, v_size_831_);
v___x_834_ = lean_nat_dec_lt(v_size_826_, v___x_833_);
lean_dec(v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_862_; 
lean_inc(v_r_830_);
lean_inc(v_l_829_);
lean_inc(v_v_828_);
lean_inc(v_k_827_);
v_isSharedCheck_862_ = !lean_is_exclusive(v_l_803_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_863_ = lean_ctor_get(v_l_803_, 4);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_l_803_, 3);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_l_803_, 2);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_l_803_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_l_803_, 0);
lean_dec(v_unused_867_);
v___x_836_ = v_l_803_;
v_isShared_837_ = v_isSharedCheck_862_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_l_803_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_862_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_852_; 
v___x_838_ = lean_nat_add(v___x_805_, v_size_814_);
v___x_839_ = lean_nat_add(v___x_838_, v_size_800_);
lean_dec(v_size_800_);
if (lean_obj_tag(v_l_829_) == 0)
{
lean_object* v_size_860_; 
v_size_860_ = lean_ctor_get(v_l_829_, 0);
lean_inc(v_size_860_);
v___y_852_ = v_size_860_;
goto v___jp_851_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___y_852_ = v___x_861_;
goto v___jp_851_;
}
v___jp_840_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_nat_add(v___y_841_, v___y_843_);
lean_dec(v___y_843_);
lean_dec(v___y_841_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 4, v_r_804_);
lean_ctor_set(v___x_836_, 3, v_r_830_);
lean_ctor_set(v___x_836_, 2, v_v_802_);
lean_ctor_set(v___x_836_, 1, v_k_801_);
lean_ctor_set(v___x_836_, 0, v___x_844_);
v___x_846_ = v___x_836_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_r_830_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_r_804_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v___x_846_);
lean_ctor_set(v___x_824_, 3, v___y_842_);
lean_ctor_set(v___x_824_, 2, v_v_828_);
lean_ctor_set(v___x_824_, 1, v_k_827_);
lean_ctor_set(v___x_824_, 0, v___x_839_);
v___x_848_ = v___x_824_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_k_827_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_v_828_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v___y_842_);
lean_ctor_set(v_reuseFailAlloc_849_, 4, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
v___jp_851_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_nat_add(v___x_838_, v___y_852_);
lean_dec(v___y_852_);
lean_dec(v___x_838_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_l_829_);
lean_ctor_set(v___x_808_, 3, v_tree_811_);
lean_ctor_set(v___x_808_, 2, v_v_813_);
lean_ctor_set(v___x_808_, 1, v_k_812_);
lean_ctor_set(v___x_808_, 0, v___x_853_);
v___x_855_ = v___x_808_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_tree_811_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_l_829_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; 
v___x_856_ = lean_nat_add(v___x_805_, v_size_831_);
if (lean_obj_tag(v_r_830_) == 0)
{
lean_object* v_size_857_; 
v_size_857_ = lean_ctor_get(v_r_830_, 0);
lean_inc(v_size_857_);
v___y_841_ = v___x_856_;
v___y_842_ = v___x_855_;
v___y_843_ = v_size_857_;
goto v___jp_840_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___y_841_ = v___x_856_;
v___y_842_ = v___x_855_;
v___y_843_ = v___x_858_;
goto v___jp_840_;
}
}
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_868_ = lean_nat_add(v___x_805_, v_size_814_);
v___x_869_ = lean_nat_add(v___x_868_, v_size_800_);
lean_dec(v_size_800_);
v___x_870_ = lean_nat_add(v___x_868_, v_size_826_);
lean_dec(v___x_868_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_l_803_);
lean_ctor_set(v___x_824_, 3, v_tree_811_);
lean_ctor_set(v___x_824_, 2, v_v_813_);
lean_ctor_set(v___x_824_, 1, v_k_812_);
lean_ctor_set(v___x_824_, 0, v___x_870_);
v___x_872_ = v___x_824_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_tree_811_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_l_803_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_r_804_);
lean_ctor_set(v___x_808_, 3, v___x_872_);
lean_ctor_set(v___x_808_, 2, v_v_802_);
lean_ctor_set(v___x_808_, 1, v_k_801_);
lean_ctor_set(v___x_808_, 0, v___x_869_);
v___x_874_ = v___x_808_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_r_804_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
else
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_936_; 
lean_inc(v_r_804_);
lean_inc(v_v_802_);
lean_inc(v_k_801_);
lean_inc(v_size_800_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; lean_object* v_unused_940_; lean_object* v_unused_941_; 
v_unused_937_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_r_623_, 2);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_r_623_, 1);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_r_623_, 0);
lean_dec(v_unused_941_);
v___x_884_ = v_r_623_;
v_isShared_885_ = v_isSharedCheck_936_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_r_623_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_936_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
if (lean_obj_tag(v_l_803_) == 0)
{
if (lean_obj_tag(v_r_804_) == 0)
{
lean_object* v_k_886_; lean_object* v_v_887_; lean_object* v_size_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_inc(v_tree_811_);
v_k_886_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_k_886_);
v_v_887_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_v_887_);
lean_dec_ref(v___x_810_);
v_size_888_ = lean_ctor_get(v_l_803_, 0);
v___x_889_ = lean_nat_add(v___x_805_, v_size_800_);
lean_dec(v_size_800_);
v___x_890_ = lean_nat_add(v___x_805_, v_size_888_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v_l_803_);
lean_ctor_set(v___x_884_, 3, v_tree_811_);
lean_ctor_set(v___x_884_, 2, v_v_887_);
lean_ctor_set(v___x_884_, 1, v_k_886_);
lean_ctor_set(v___x_884_, 0, v___x_890_);
v___x_892_ = v___x_884_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_tree_811_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_l_803_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_r_804_);
lean_ctor_set(v___x_808_, 3, v___x_892_);
lean_ctor_set(v___x_808_, 2, v_v_802_);
lean_ctor_set(v___x_808_, 1, v_k_801_);
lean_ctor_set(v___x_808_, 0, v___x_889_);
v___x_894_ = v___x_808_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_r_804_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_size_800_);
v_k_897_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_k_897_);
v_v_898_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_v_898_);
lean_dec_ref(v___x_810_);
v_k_899_ = lean_ctor_get(v_l_803_, 1);
v_v_900_ = lean_ctor_get(v_l_803_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_l_803_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_915_ = lean_ctor_get(v_l_803_, 4);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_l_803_, 3);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_l_803_, 0);
lean_dec(v_unused_917_);
v___x_902_ = v_l_803_;
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_v_900_);
lean_inc(v_k_899_);
lean_dec(v_l_803_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_unsigned_to_nat(3u);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_804_);
lean_ctor_set(v___x_902_, 3, v_r_804_);
lean_ctor_set(v___x_902_, 2, v_v_898_);
lean_ctor_set(v___x_902_, 1, v_k_897_);
lean_ctor_set(v___x_902_, 0, v___x_805_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_804_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_804_);
v___x_906_ = v_reuseFailAlloc_913_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 3, v_r_804_);
lean_ctor_set(v___x_884_, 0, v___x_805_);
v___x_908_ = v___x_884_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_r_804_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_r_804_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v___x_908_);
lean_ctor_set(v___x_808_, 3, v___x_906_);
lean_ctor_set(v___x_808_, 2, v_v_900_);
lean_ctor_set(v___x_808_, 1, v_k_899_);
lean_ctor_set(v___x_808_, 0, v___x_904_);
v___x_910_ = v___x_808_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_804_) == 0)
{
lean_object* v_k_918_; lean_object* v_v_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v_size_800_);
v_k_918_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_k_918_);
v_v_919_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_v_919_);
lean_dec_ref(v___x_810_);
v___x_920_ = lean_unsigned_to_nat(3u);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v_l_803_);
lean_ctor_set(v___x_884_, 2, v_v_919_);
lean_ctor_set(v___x_884_, 1, v_k_918_);
lean_ctor_set(v___x_884_, 0, v___x_805_);
v___x_922_ = v___x_884_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_918_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_919_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_l_803_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_l_803_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_r_804_);
lean_ctor_set(v___x_808_, 3, v___x_922_);
lean_ctor_set(v___x_808_, 2, v_v_802_);
lean_ctor_set(v___x_808_, 1, v_k_801_);
lean_ctor_set(v___x_808_, 0, v___x_920_);
v___x_924_ = v___x_808_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_r_804_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v___x_930_; 
v_k_927_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_k_927_);
v_v_928_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_v_928_);
lean_dec_ref(v___x_810_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 3, v_r_804_);
v___x_930_ = v___x_884_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_size_800_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_r_804_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_r_804_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(2u);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v___x_930_);
lean_ctor_set(v___x_808_, 3, v_r_804_);
lean_ctor_set(v___x_808_, 2, v_v_928_);
lean_ctor_set(v___x_808_, 1, v_k_927_);
lean_ctor_set(v___x_808_, 0, v___x_931_);
v___x_933_ = v___x_808_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_r_804_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v___x_930_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
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
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_1100_; 
lean_inc(v_r_804_);
lean_inc(v_v_802_);
lean_inc(v_k_801_);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1101_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_r_623_, 2);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_r_623_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_r_623_, 0);
lean_dec(v_unused_1105_);
v___x_949_ = v_r_623_;
v_isShared_950_ = v_isSharedCheck_1100_;
goto v_resetjp_948_;
}
else
{
lean_dec(v_r_623_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_1100_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v_tree_952_; 
v___x_951_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_801_, v_v_802_, v_l_803_, v_r_804_);
v_tree_952_ = lean_ctor_get(v___x_951_, 2);
lean_inc(v_tree_952_);
if (lean_obj_tag(v_tree_952_) == 0)
{
lean_object* v_k_953_; lean_object* v_v_954_; lean_object* v_size_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_k_953_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_k_953_);
v_v_954_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_v_954_);
lean_dec_ref(v___x_951_);
v_size_955_ = lean_ctor_get(v_tree_952_, 0);
v___x_956_ = lean_unsigned_to_nat(3u);
v___x_957_ = lean_nat_mul(v___x_956_, v_size_955_);
v___x_958_ = lean_nat_dec_lt(v___x_957_, v_size_795_);
lean_dec(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec(v_r_799_);
v___x_959_ = lean_nat_add(v___x_805_, v_size_795_);
v___x_960_ = lean_nat_add(v___x_959_, v_size_955_);
lean_dec(v___x_959_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_tree_952_);
lean_ctor_set(v___x_949_, 3, v_l_622_);
lean_ctor_set(v___x_949_, 2, v_v_954_);
lean_ctor_set(v___x_949_, 1, v_k_953_);
lean_ctor_set(v___x_949_, 0, v___x_960_);
v___x_962_ = v___x_949_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_k_953_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_v_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_tree_952_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1029_; 
lean_inc(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
lean_inc(v_size_795_);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; lean_object* v_unused_1034_; 
v_unused_1030_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_l_622_, 2);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_l_622_, 1);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_1034_);
v___x_965_ = v_l_622_;
v_isShared_966_ = v_isSharedCheck_1029_;
goto v_resetjp_964_;
}
else
{
lean_dec(v_l_622_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1029_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_size_967_; lean_object* v_size_968_; lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v_l_971_; lean_object* v_r_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_size_967_ = lean_ctor_get(v_l_798_, 0);
v_size_968_ = lean_ctor_get(v_r_799_, 0);
v_k_969_ = lean_ctor_get(v_r_799_, 1);
v_v_970_ = lean_ctor_get(v_r_799_, 2);
v_l_971_ = lean_ctor_get(v_r_799_, 3);
v_r_972_ = lean_ctor_get(v_r_799_, 4);
v___x_973_ = lean_unsigned_to_nat(2u);
v___x_974_ = lean_nat_mul(v___x_973_, v_size_967_);
v___x_975_ = lean_nat_dec_lt(v_size_968_, v___x_974_);
lean_dec(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1013_; 
lean_inc(v_r_972_);
lean_inc(v_l_971_);
lean_inc(v_v_970_);
lean_inc(v_k_969_);
lean_del_object(v___x_965_);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_r_799_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1014_ = lean_ctor_get(v_r_799_, 4);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_r_799_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_r_799_, 2);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_799_, 1);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_799_, 0);
lean_dec(v_unused_1018_);
v___x_977_ = v_r_799_;
v_isShared_978_ = v_isSharedCheck_1013_;
goto v_resetjp_976_;
}
else
{
lean_dec(v_r_799_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1013_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___x_1001_; lean_object* v___y_1003_; 
v___x_979_ = lean_nat_add(v___x_805_, v_size_795_);
lean_dec(v_size_795_);
v___x_980_ = lean_nat_add(v___x_979_, v_size_955_);
lean_dec(v___x_979_);
v___x_1001_ = lean_nat_add(v___x_805_, v_size_967_);
if (lean_obj_tag(v_l_971_) == 0)
{
lean_object* v_size_1011_; 
v_size_1011_ = lean_ctor_get(v_l_971_, 0);
lean_inc(v_size_1011_);
v___y_1003_ = v_size_1011_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
v___y_1003_ = v___x_1012_;
goto v___jp_1002_;
}
v___jp_981_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_nat_add(v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec(v___y_983_);
lean_inc_ref(v_tree_952_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 4, v_tree_952_);
lean_ctor_set(v___x_977_, 3, v_r_972_);
lean_ctor_set(v___x_977_, 2, v_v_954_);
lean_ctor_set(v___x_977_, 1, v_k_953_);
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_k_953_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_v_954_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_r_972_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_tree_952_);
v___x_987_ = v_reuseFailAlloc_1000_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_isSharedCheck_994_ = !lean_is_exclusive(v_tree_952_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_995_ = lean_ctor_get(v_tree_952_, 4);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_tree_952_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_tree_952_, 2);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_tree_952_, 1);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_tree_952_, 0);
lean_dec(v_unused_999_);
v___x_989_ = v_tree_952_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_dec(v_tree_952_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 4, v___x_987_);
lean_ctor_set(v___x_989_, 3, v___y_982_);
lean_ctor_set(v___x_989_, 2, v_v_970_);
lean_ctor_set(v___x_989_, 1, v_k_969_);
lean_ctor_set(v___x_989_, 0, v___x_980_);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_969_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_970_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v___y_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v___x_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
v___jp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_nat_add(v___x_1001_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec(v___x_1001_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_l_971_);
lean_ctor_set(v___x_949_, 3, v_l_798_);
lean_ctor_set(v___x_949_, 2, v_v_797_);
lean_ctor_set(v___x_949_, 1, v_k_796_);
lean_ctor_set(v___x_949_, 0, v___x_1004_);
v___x_1006_ = v___x_949_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_l_798_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_l_971_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_nat_add(v___x_805_, v_size_955_);
if (lean_obj_tag(v_r_972_) == 0)
{
lean_object* v_size_1008_; 
v_size_1008_ = lean_ctor_get(v_r_972_, 0);
lean_inc(v_size_1008_);
v___y_982_ = v___x_1006_;
v___y_983_ = v___x_1007_;
v___y_984_ = v_size_1008_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___y_982_ = v___x_1006_;
v___y_983_ = v___x_1007_;
v___y_984_ = v___x_1009_;
goto v___jp_981_;
}
}
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1019_ = lean_nat_add(v___x_805_, v_size_795_);
lean_dec(v_size_795_);
v___x_1020_ = lean_nat_add(v___x_1019_, v_size_955_);
lean_dec(v___x_1019_);
v___x_1021_ = lean_nat_add(v___x_805_, v_size_955_);
v___x_1022_ = lean_nat_add(v___x_1021_, v_size_968_);
lean_dec(v___x_1021_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_tree_952_);
lean_ctor_set(v___x_949_, 3, v_r_799_);
lean_ctor_set(v___x_949_, 2, v_v_954_);
lean_ctor_set(v___x_949_, 1, v_k_953_);
lean_ctor_set(v___x_949_, 0, v___x_1022_);
v___x_1024_ = v___x_949_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_k_953_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_v_954_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_r_799_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_tree_952_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v___x_1024_);
lean_ctor_set(v___x_965_, 0, v___x_1020_);
v___x_1026_ = v___x_965_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_l_798_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_798_) == 0)
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1058_; 
lean_inc_ref(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
lean_inc(v_size_795_);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; lean_object* v_unused_1063_; 
v_unused_1059_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_l_622_, 2);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_l_622_, 1);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_1063_);
v___x_1036_ = v_l_622_;
v_isShared_1037_ = v_isSharedCheck_1058_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_l_622_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1058_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
if (lean_obj_tag(v_r_799_) == 0)
{
lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v_size_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_k_1038_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_k_1038_);
v_v_1039_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_v_1039_);
lean_dec_ref(v___x_951_);
v_size_1040_ = lean_ctor_get(v_r_799_, 0);
v___x_1041_ = lean_nat_add(v___x_805_, v_size_795_);
lean_dec(v_size_795_);
v___x_1042_ = lean_nat_add(v___x_805_, v_size_1040_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_tree_952_);
lean_ctor_set(v___x_949_, 3, v_r_799_);
lean_ctor_set(v___x_949_, 2, v_v_1039_);
lean_ctor_set(v___x_949_, 1, v_k_1038_);
lean_ctor_set(v___x_949_, 0, v___x_1042_);
v___x_1044_ = v___x_949_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_r_799_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_tree_952_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1044_);
lean_ctor_set(v___x_1036_, 0, v___x_1041_);
v___x_1046_ = v___x_1036_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_l_798_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
lean_object* v_k_1049_; lean_object* v_v_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_dec(v_size_795_);
v_k_1049_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_k_1049_);
v_v_1050_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_v_1050_);
lean_dec_ref(v___x_951_);
v___x_1051_ = lean_unsigned_to_nat(3u);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_r_799_);
lean_ctor_set(v___x_949_, 3, v_r_799_);
lean_ctor_set(v___x_949_, 2, v_v_1050_);
lean_ctor_set(v___x_949_, 1, v_k_1049_);
lean_ctor_set(v___x_949_, 0, v___x_805_);
v___x_1053_ = v___x_949_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_r_799_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_r_799_);
v___x_1053_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1053_);
lean_ctor_set(v___x_1036_, 0, v___x_1051_);
v___x_1055_ = v___x_1036_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_l_798_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_799_) == 0)
{
lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1088_; 
lean_inc(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1089_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_l_622_, 2);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_l_622_, 1);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_1093_);
v___x_1065_ = v_l_622_;
v_isShared_1066_ = v_isSharedCheck_1088_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v_l_622_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1088_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_k_1067_; lean_object* v_v_1068_; lean_object* v_k_1069_; lean_object* v_v_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1084_; 
v_k_1067_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_k_1067_);
v_v_1068_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_v_1068_);
lean_dec_ref(v___x_951_);
v_k_1069_ = lean_ctor_get(v_r_799_, 1);
v_v_1070_ = lean_ctor_get(v_r_799_, 2);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_r_799_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1085_ = lean_ctor_get(v_r_799_, 4);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_r_799_, 3);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_r_799_, 0);
lean_dec(v_unused_1087_);
v___x_1072_ = v_r_799_;
v_isShared_1073_ = v_isSharedCheck_1084_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_v_1070_);
lean_inc(v_k_1069_);
lean_dec(v_r_799_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1084_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_unsigned_to_nat(3u);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_l_798_);
lean_ctor_set(v___x_1072_, 3, v_l_798_);
lean_ctor_set(v___x_1072_, 2, v_v_797_);
lean_ctor_set(v___x_1072_, 1, v_k_796_);
lean_ctor_set(v___x_1072_, 0, v___x_805_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_l_798_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_l_798_);
v___x_1076_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_l_798_);
lean_ctor_set(v___x_949_, 3, v_l_798_);
lean_ctor_set(v___x_949_, 2, v_v_1068_);
lean_ctor_set(v___x_949_, 1, v_k_1067_);
lean_ctor_set(v___x_949_, 0, v___x_805_);
v___x_1078_ = v___x_949_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_l_798_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_l_798_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1078_);
lean_ctor_set(v___x_1065_, 3, v___x_1076_);
lean_ctor_set(v___x_1065_, 2, v_v_1070_);
lean_ctor_set(v___x_1065_, 1, v_k_1069_);
lean_ctor_set(v___x_1065_, 0, v___x_1074_);
v___x_1080_ = v___x_1065_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_k_1069_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_v_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
else
{
lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v_k_1094_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_k_1094_);
v_v_1095_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_v_1095_);
lean_dec_ref(v___x_951_);
v___x_1096_ = lean_unsigned_to_nat(2u);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_r_799_);
lean_ctor_set(v___x_949_, 3, v_l_622_);
lean_ctor_set(v___x_949_, 2, v_v_1095_);
lean_ctor_set(v___x_949_, 1, v_k_1094_);
lean_ctor_set(v___x_949_, 0, v___x_1096_);
v___x_1098_ = v___x_949_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_r_799_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
}
else
{
return v_l_622_;
}
}
else
{
return v_r_623_;
}
}
}
else
{
lean_object* v_impl_1106_; lean_object* v___x_1107_; 
v_impl_1106_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_618_, v_l_622_);
v___x_1107_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1106_) == 0)
{
if (lean_obj_tag(v_r_623_) == 0)
{
lean_object* v_size_1108_; lean_object* v_size_1109_; lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v_l_1112_; lean_object* v_r_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_size_1108_ = lean_ctor_get(v_impl_1106_, 0);
v_size_1109_ = lean_ctor_get(v_r_623_, 0);
v_k_1110_ = lean_ctor_get(v_r_623_, 1);
v_v_1111_ = lean_ctor_get(v_r_623_, 2);
v_l_1112_ = lean_ctor_get(v_r_623_, 3);
lean_inc(v_l_1112_);
v_r_1113_ = lean_ctor_get(v_r_623_, 4);
v___x_1114_ = lean_unsigned_to_nat(3u);
v___x_1115_ = lean_nat_mul(v___x_1114_, v_size_1108_);
v___x_1116_ = lean_nat_dec_lt(v___x_1115_, v_size_1109_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec(v_l_1112_);
v___x_1117_ = lean_nat_add(v___x_1107_, v_size_1108_);
v___x_1118_ = lean_nat_add(v___x_1117_, v_size_1109_);
lean_dec(v___x_1117_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 3, v_impl_1106_);
lean_ctor_set(v___x_625_, 0, v___x_1118_);
v___x_1120_ = v___x_625_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_r_623_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1185_; 
lean_inc(v_r_1113_);
lean_inc(v_v_1111_);
lean_inc(v_k_1110_);
lean_inc(v_size_1109_);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1186_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_r_623_, 2);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_r_623_, 1);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_r_623_, 0);
lean_dec(v_unused_1190_);
v___x_1123_ = v_r_623_;
v_isShared_1124_ = v_isSharedCheck_1185_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v_r_623_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1185_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_size_1125_; lean_object* v_k_1126_; lean_object* v_v_1127_; lean_object* v_l_1128_; lean_object* v_r_1129_; lean_object* v_size_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_size_1125_ = lean_ctor_get(v_l_1112_, 0);
v_k_1126_ = lean_ctor_get(v_l_1112_, 1);
v_v_1127_ = lean_ctor_get(v_l_1112_, 2);
v_l_1128_ = lean_ctor_get(v_l_1112_, 3);
v_r_1129_ = lean_ctor_get(v_l_1112_, 4);
v_size_1130_ = lean_ctor_get(v_r_1113_, 0);
v___x_1131_ = lean_unsigned_to_nat(2u);
v___x_1132_ = lean_nat_mul(v___x_1131_, v_size_1130_);
v___x_1133_ = lean_nat_dec_lt(v_size_1125_, v___x_1132_);
lean_dec(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1161_; 
lean_inc(v_r_1129_);
lean_inc(v_l_1128_);
lean_inc(v_v_1127_);
lean_inc(v_k_1126_);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_l_1112_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; 
v_unused_1162_ = lean_ctor_get(v_l_1112_, 4);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_l_1112_, 3);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_l_1112_, 2);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_l_1112_, 1);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_l_1112_, 0);
lean_dec(v_unused_1166_);
v___x_1135_ = v_l_1112_;
v_isShared_1136_ = v_isSharedCheck_1161_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v_l_1112_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1161_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1151_; 
v___x_1137_ = lean_nat_add(v___x_1107_, v_size_1108_);
v___x_1138_ = lean_nat_add(v___x_1137_, v_size_1109_);
lean_dec(v_size_1109_);
if (lean_obj_tag(v_l_1128_) == 0)
{
lean_object* v_size_1159_; 
v_size_1159_ = lean_ctor_get(v_l_1128_, 0);
lean_inc(v_size_1159_);
v___y_1151_ = v_size_1159_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___y_1151_ = v___x_1160_;
goto v___jp_1150_;
}
v___jp_1139_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_nat_add(v___y_1140_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v___y_1140_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 4, v_r_1113_);
lean_ctor_set(v___x_1135_, 3, v_r_1129_);
lean_ctor_set(v___x_1135_, 2, v_v_1111_);
lean_ctor_set(v___x_1135_, 1, v_k_1110_);
lean_ctor_set(v___x_1135_, 0, v___x_1143_);
v___x_1145_ = v___x_1135_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_r_1129_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_r_1113_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v___x_1145_);
lean_ctor_set(v___x_1123_, 3, v___y_1141_);
lean_ctor_set(v___x_1123_, 2, v_v_1127_);
lean_ctor_set(v___x_1123_, 1, v_k_1126_);
lean_ctor_set(v___x_1123_, 0, v___x_1138_);
v___x_1147_ = v___x_1123_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1126_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1127_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v___y_1141_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_nat_add(v___x_1137_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec(v___x_1137_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_l_1128_);
lean_ctor_set(v___x_625_, 3, v_impl_1106_);
lean_ctor_set(v___x_625_, 0, v___x_1152_);
v___x_1154_ = v___x_625_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_l_1128_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_nat_add(v___x_1107_, v_size_1130_);
if (lean_obj_tag(v_r_1129_) == 0)
{
lean_object* v_size_1156_; 
v_size_1156_ = lean_ctor_get(v_r_1129_, 0);
lean_inc(v_size_1156_);
v___y_1140_ = v___x_1155_;
v___y_1141_ = v___x_1154_;
v___y_1142_ = v_size_1156_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___y_1140_ = v___x_1155_;
v___y_1141_ = v___x_1154_;
v___y_1142_ = v___x_1157_;
goto v___jp_1139_;
}
}
}
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_del_object(v___x_625_);
v___x_1167_ = lean_nat_add(v___x_1107_, v_size_1108_);
v___x_1168_ = lean_nat_add(v___x_1167_, v_size_1109_);
lean_dec(v_size_1109_);
v___x_1169_ = lean_nat_add(v___x_1167_, v_size_1125_);
lean_dec(v___x_1167_);
lean_inc_ref(v_impl_1106_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v_l_1112_);
lean_ctor_set(v___x_1123_, 3, v_impl_1106_);
lean_ctor_set(v___x_1123_, 2, v_v_621_);
lean_ctor_set(v___x_1123_, 1, v_k_620_);
lean_ctor_set(v___x_1123_, 0, v___x_1169_);
v___x_1171_ = v___x_1123_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_l_1112_);
v___x_1171_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_isSharedCheck_1178_ = !lean_is_exclusive(v_impl_1106_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1179_ = lean_ctor_get(v_impl_1106_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_impl_1106_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_impl_1106_, 2);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_impl_1106_, 1);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_impl_1106_, 0);
lean_dec(v_unused_1183_);
v___x_1173_ = v_impl_1106_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_dec(v_impl_1106_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 4, v_r_1113_);
lean_ctor_set(v___x_1173_, 3, v___x_1171_);
lean_ctor_set(v___x_1173_, 2, v_v_1111_);
lean_ctor_set(v___x_1173_, 1, v_k_1110_);
lean_ctor_set(v___x_1173_, 0, v___x_1168_);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_r_1113_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_size_1191_ = lean_ctor_get(v_impl_1106_, 0);
v___x_1192_ = lean_nat_add(v___x_1107_, v_size_1191_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 3, v_impl_1106_);
lean_ctor_set(v___x_625_, 0, v___x_1192_);
v___x_1194_ = v___x_625_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_r_623_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
if (lean_obj_tag(v_r_623_) == 0)
{
lean_object* v_l_1196_; 
v_l_1196_ = lean_ctor_get(v_r_623_, 3);
lean_inc(v_l_1196_);
if (lean_obj_tag(v_l_1196_) == 0)
{
lean_object* v_r_1197_; 
v_r_1197_ = lean_ctor_get(v_r_623_, 4);
lean_inc(v_r_1197_);
if (lean_obj_tag(v_r_1197_) == 0)
{
lean_object* v_size_1198_; lean_object* v_k_1199_; lean_object* v_v_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1213_; 
v_size_1198_ = lean_ctor_get(v_r_623_, 0);
v_k_1199_ = lean_ctor_get(v_r_623_, 1);
v_v_1200_ = lean_ctor_get(v_r_623_, 2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; lean_object* v_unused_1215_; 
v_unused_1214_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_1215_);
v___x_1202_ = v_r_623_;
v_isShared_1203_ = v_isSharedCheck_1213_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_v_1200_);
lean_inc(v_k_1199_);
lean_inc(v_size_1198_);
lean_dec(v_r_623_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1213_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_size_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v_size_1204_ = lean_ctor_get(v_l_1196_, 0);
v___x_1205_ = lean_nat_add(v___x_1107_, v_size_1198_);
lean_dec(v_size_1198_);
v___x_1206_ = lean_nat_add(v___x_1107_, v_size_1204_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 4, v_l_1196_);
lean_ctor_set(v___x_1202_, 3, v_impl_1106_);
lean_ctor_set(v___x_1202_, 2, v_v_621_);
lean_ctor_set(v___x_1202_, 1, v_k_620_);
lean_ctor_set(v___x_1202_, 0, v___x_1206_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_l_1196_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_r_1197_);
lean_ctor_set(v___x_625_, 3, v___x_1208_);
lean_ctor_set(v___x_625_, 2, v_v_1200_);
lean_ctor_set(v___x_625_, 1, v_k_1199_);
lean_ctor_set(v___x_625_, 0, v___x_1205_);
v___x_1210_ = v___x_625_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_k_1199_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_v_1200_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_r_1197_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1240_; 
v_k_1216_ = lean_ctor_get(v_r_623_, 1);
v_v_1217_ = lean_ctor_get(v_r_623_, 2);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; lean_object* v_unused_1242_; lean_object* v_unused_1243_; 
v_unused_1241_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_1241_);
v_unused_1242_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_r_623_, 0);
lean_dec(v_unused_1243_);
v___x_1219_ = v_r_623_;
v_isShared_1220_ = v_isSharedCheck_1240_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
lean_dec(v_r_623_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1240_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_k_1221_; lean_object* v_v_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1236_; 
v_k_1221_ = lean_ctor_get(v_l_1196_, 1);
v_v_1222_ = lean_ctor_get(v_l_1196_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_l_1196_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; 
v_unused_1237_ = lean_ctor_get(v_l_1196_, 4);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_l_1196_, 3);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_l_1196_, 0);
lean_dec(v_unused_1239_);
v___x_1224_ = v_l_1196_;
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_v_1222_);
lean_inc(v_k_1221_);
lean_dec(v_l_1196_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_unsigned_to_nat(3u);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 4, v_r_1197_);
lean_ctor_set(v___x_1224_, 3, v_r_1197_);
lean_ctor_set(v___x_1224_, 2, v_v_621_);
lean_ctor_set(v___x_1224_, 1, v_k_620_);
lean_ctor_set(v___x_1224_, 0, v___x_1107_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_r_1197_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_r_1197_);
v___x_1228_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 3, v_r_1197_);
lean_ctor_set(v___x_1219_, 0, v___x_1107_);
v___x_1230_ = v___x_1219_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_r_1197_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v_r_1197_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_1230_);
lean_ctor_set(v___x_625_, 3, v___x_1228_);
lean_ctor_set(v___x_625_, 2, v_v_1222_);
lean_ctor_set(v___x_625_, 1, v_k_1221_);
lean_ctor_set(v___x_625_, 0, v___x_1226_);
v___x_1232_ = v___x_625_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1221_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1222_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1244_; 
v_r_1244_ = lean_ctor_get(v_r_623_, 4);
lean_inc(v_r_1244_);
if (lean_obj_tag(v_r_1244_) == 0)
{
lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
v_k_1245_ = lean_ctor_get(v_r_623_, 1);
v_v_1246_ = lean_ctor_get(v_r_623_, 2);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1258_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_1258_);
v_unused_1259_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v_r_623_, 0);
lean_dec(v_unused_1260_);
v___x_1248_ = v_r_623_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
lean_dec(v_r_623_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(3u);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 4, v_l_1196_);
lean_ctor_set(v___x_1248_, 2, v_v_621_);
lean_ctor_set(v___x_1248_, 1, v_k_620_);
lean_ctor_set(v___x_1248_, 0, v___x_1107_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_l_1196_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_l_1196_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_r_1244_);
lean_ctor_set(v___x_625_, 3, v___x_1252_);
lean_ctor_set(v___x_625_, 2, v_v_1246_);
lean_ctor_set(v___x_625_, 1, v_k_1245_);
lean_ctor_set(v___x_625_, 0, v___x_1250_);
v___x_1254_ = v___x_625_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_r_1244_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_size_1261_; lean_object* v_k_1262_; lean_object* v_v_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1274_; 
v_size_1261_ = lean_ctor_get(v_r_623_, 0);
v_k_1262_ = lean_ctor_get(v_r_623_, 1);
v_v_1263_ = lean_ctor_get(v_r_623_, 2);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_r_623_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; lean_object* v_unused_1276_; 
v_unused_1275_ = lean_ctor_get(v_r_623_, 4);
lean_dec(v_unused_1275_);
v_unused_1276_ = lean_ctor_get(v_r_623_, 3);
lean_dec(v_unused_1276_);
v___x_1265_ = v_r_623_;
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_v_1263_);
lean_inc(v_k_1262_);
lean_inc(v_size_1261_);
lean_dec(v_r_623_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 3, v_r_1244_);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_size_1261_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_r_1244_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_r_1244_);
v___x_1268_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_unsigned_to_nat(2u);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_1268_);
lean_ctor_set(v___x_625_, 3, v_r_1244_);
lean_ctor_set(v___x_625_, 0, v___x_1269_);
v___x_1271_ = v___x_625_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_r_1244_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v___x_1268_);
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
lean_object* v___x_1278_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 3, v_r_623_);
lean_ctor_set(v___x_625_, 0, v___x_1107_);
v___x_1278_ = v___x_625_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_r_623_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_r_623_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
else
{
return v_t_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg___boxed(lean_object* v_k_1282_, lean_object* v_t_1283_){
_start:
{
uint64_t v_k_boxed_1284_; lean_object* v_res_1285_; 
v_k_boxed_1284_ = lean_unbox_uint64(v_k_1282_);
lean_dec_ref(v_k_1282_);
v_res_1285_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_boxed_1284_, v_t_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t v_h_1286_, lean_object* v_st_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_h_1286_, v_st_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object* v_h_1289_, lean_object* v_st_1290_){
_start:
{
uint64_t v_h_boxed_1291_; lean_object* v_res_1292_; 
v_h_boxed_1291_ = lean_unbox_uint64(v_h_1289_);
lean_dec_ref(v_h_1289_);
v_res_1292_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_1291_, v_st_1290_);
return v_res_1292_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg___closed__0);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16___redArg();
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_ctor_set(v___x_1302_, 2, v___x_1300_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1303_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__4, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__4_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__4);
v___x_1304_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
v___x_1305_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1306_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
v___x_1307_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v___x_1304_);
lean_ctor_set(v___x_1307_, 3, v___x_1305_);
lean_ctor_set(v___x_1307_, 4, v___x_1305_);
lean_ctor_set(v___x_1307_, 5, v___x_1305_);
lean_ctor_set(v___x_1307_, 6, v___x_1305_);
lean_ctor_set(v___x_1307_, 7, v___x_1303_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v_env_1315_; lean_object* v_nextMacroScope_1316_; lean_object* v_ngen_1317_; lean_object* v_auxDeclNGen_1318_; lean_object* v_traceState_1319_; lean_object* v_recordedDeps_1320_; lean_object* v_messages_1321_; lean_object* v_infoState_1322_; lean_object* v_snapshotTasks_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1351_; 
v___x_1312_ = lean_box_uint64(v_h_1308_);
v___f_1313_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1313_, 0, v___x_1312_);
v___x_1314_ = lean_st_ref_take(v___y_1310_);
v_env_1315_ = lean_ctor_get(v___x_1314_, 0);
v_nextMacroScope_1316_ = lean_ctor_get(v___x_1314_, 1);
v_ngen_1317_ = lean_ctor_get(v___x_1314_, 2);
v_auxDeclNGen_1318_ = lean_ctor_get(v___x_1314_, 3);
v_traceState_1319_ = lean_ctor_get(v___x_1314_, 4);
v_recordedDeps_1320_ = lean_ctor_get(v___x_1314_, 6);
v_messages_1321_ = lean_ctor_get(v___x_1314_, 7);
v_infoState_1322_ = lean_ctor_get(v___x_1314_, 8);
v_snapshotTasks_1323_ = lean_ctor_get(v___x_1314_, 9);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v___x_1314_, 5);
lean_dec(v_unused_1352_);
v___x_1325_ = v___x_1314_;
v_isShared_1326_ = v_isSharedCheck_1351_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_snapshotTasks_1323_);
lean_inc(v_infoState_1322_);
lean_inc(v_messages_1321_);
lean_inc(v_recordedDeps_1320_);
lean_inc(v_traceState_1319_);
lean_inc(v_auxDeclNGen_1318_);
lean_inc(v_ngen_1317_);
lean_inc(v_nextMacroScope_1316_);
lean_inc(v_env_1315_);
lean_dec(v___x_1314_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1351_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1327_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1328_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1327_, v_env_1315_, v___f_1313_);
v___x_1329_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 5, v___x_1329_);
lean_ctor_set(v___x_1325_, 0, v___x_1328_);
v___x_1331_ = v___x_1325_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_nextMacroScope_1316_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_ngen_1317_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_auxDeclNGen_1318_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_traceState_1319_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1350_, 6, v_recordedDeps_1320_);
lean_ctor_set(v_reuseFailAlloc_1350_, 7, v_messages_1321_);
lean_ctor_set(v_reuseFailAlloc_1350_, 8, v_infoState_1322_);
lean_ctor_set(v_reuseFailAlloc_1350_, 9, v_snapshotTasks_1323_);
v___x_1331_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_mctx_1334_; lean_object* v_zetaDeltaFVarIds_1335_; lean_object* v_postponed_1336_; lean_object* v_diag_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1348_; 
v___x_1332_ = lean_st_ref_put(v___y_1310_, v___x_1331_);
v___x_1333_ = lean_st_ref_take(v___y_1309_);
v_mctx_1334_ = lean_ctor_get(v___x_1333_, 0);
v_zetaDeltaFVarIds_1335_ = lean_ctor_get(v___x_1333_, 2);
v_postponed_1336_ = lean_ctor_get(v___x_1333_, 3);
v_diag_1337_ = lean_ctor_get(v___x_1333_, 4);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v___x_1333_, 1);
lean_dec(v_unused_1349_);
v___x_1339_ = v___x_1333_;
v_isShared_1340_ = v_isSharedCheck_1348_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_diag_1337_);
lean_inc(v_postponed_1336_);
lean_inc(v_zetaDeltaFVarIds_1335_);
lean_inc(v_mctx_1334_);
lean_dec(v___x_1333_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1348_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_mctx_1334_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_zetaDeltaFVarIds_1335_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_postponed_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_diag_1337_);
v___x_1344_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_st_ref_put(v___y_1309_, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1341_);
return v___x_1346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint64_t v_h_boxed_1357_; lean_object* v_res_1358_; 
v_h_boxed_1357_ = lean_unbox_uint64(v_h_1353_);
lean_dec_ref(v_h_1353_);
v_res_1358_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1357_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1359_, uint64_t v_k_1360_, lean_object* v_fallback_1361_){
_start:
{
if (lean_obj_tag(v_t_1359_) == 0)
{
lean_object* v_k_1362_; lean_object* v_v_1363_; lean_object* v_l_1364_; lean_object* v_r_1365_; uint64_t v___x_1366_; uint8_t v___x_1367_; 
v_k_1362_ = lean_ctor_get(v_t_1359_, 1);
v_v_1363_ = lean_ctor_get(v_t_1359_, 2);
v_l_1364_ = lean_ctor_get(v_t_1359_, 3);
v_r_1365_ = lean_ctor_get(v_t_1359_, 4);
v___x_1366_ = lean_unbox_uint64(v_k_1362_);
v___x_1367_ = lean_uint64_dec_lt(v_k_1360_, v___x_1366_);
if (v___x_1367_ == 0)
{
uint64_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_unbox_uint64(v_k_1362_);
v___x_1369_ = lean_uint64_dec_eq(v_k_1360_, v___x_1368_);
if (v___x_1369_ == 0)
{
v_t_1359_ = v_r_1365_;
goto _start;
}
else
{
lean_inc(v_v_1363_);
return v_v_1363_;
}
}
else
{
v_t_1359_ = v_l_1364_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1361_);
return v_fallback_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1372_, lean_object* v_k_1373_, lean_object* v_fallback_1374_){
_start:
{
uint64_t v_k_boxed_1375_; lean_object* v_res_1376_; 
v_k_boxed_1375_ = lean_unbox_uint64(v_k_1373_);
lean_dec_ref(v_k_1373_);
v_res_1376_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1372_, v_k_boxed_1375_, v_fallback_1374_);
lean_dec(v_fallback_1374_);
lean_dec(v_t_1372_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1377_, lean_object* v_v_1378_, lean_object* v_t_1379_){
_start:
{
if (lean_obj_tag(v_t_1379_) == 0)
{
lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_l_1383_; lean_object* v_r_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1668_; 
v_size_1380_ = lean_ctor_get(v_t_1379_, 0);
v_k_1381_ = lean_ctor_get(v_t_1379_, 1);
v_v_1382_ = lean_ctor_get(v_t_1379_, 2);
v_l_1383_ = lean_ctor_get(v_t_1379_, 3);
v_r_1384_ = lean_ctor_get(v_t_1379_, 4);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_t_1379_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1386_ = v_t_1379_;
v_isShared_1387_ = v_isSharedCheck_1668_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_r_1384_);
lean_inc(v_l_1383_);
lean_inc(v_v_1382_);
lean_inc(v_k_1381_);
lean_inc(v_size_1380_);
lean_dec(v_t_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1668_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint64_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = lean_unbox_uint64(v_k_1381_);
v___x_1389_ = lean_uint64_dec_lt(v_k_1377_, v___x_1388_);
if (v___x_1389_ == 0)
{
uint64_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_unbox_uint64(v_k_1381_);
v___x_1391_ = lean_uint64_dec_eq(v_k_1377_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v_impl_1392_; lean_object* v___x_1393_; 
lean_dec(v_size_1380_);
v_impl_1392_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1377_, v_v_1378_, v_r_1384_);
v___x_1393_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1383_) == 0)
{
lean_object* v_size_1394_; lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_l_1398_; lean_object* v_r_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1394_ = lean_ctor_get(v_l_1383_, 0);
v_size_1395_ = lean_ctor_get(v_impl_1392_, 0);
v_k_1396_ = lean_ctor_get(v_impl_1392_, 1);
v_v_1397_ = lean_ctor_get(v_impl_1392_, 2);
v_l_1398_ = lean_ctor_get(v_impl_1392_, 3);
lean_inc(v_l_1398_);
v_r_1399_ = lean_ctor_get(v_impl_1392_, 4);
v___x_1400_ = lean_unsigned_to_nat(3u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1394_);
v___x_1402_ = lean_nat_dec_lt(v___x_1401_, v_size_1395_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_dec(v_l_1398_);
v___x_1403_ = lean_nat_add(v___x_1393_, v_size_1394_);
v___x_1404_ = lean_nat_add(v___x_1403_, v_size_1395_);
lean_dec(v___x_1403_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_impl_1392_);
lean_ctor_set(v___x_1386_, 0, v___x_1404_);
v___x_1406_ = v___x_1386_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v_impl_1392_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1471_; 
lean_inc(v_r_1399_);
lean_inc(v_v_1397_);
lean_inc(v_k_1396_);
lean_inc(v_size_1395_);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_impl_1392_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; 
v_unused_1472_ = lean_ctor_get(v_impl_1392_, 4);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_impl_1392_, 3);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_impl_1392_, 2);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_impl_1392_, 1);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_impl_1392_, 0);
lean_dec(v_unused_1476_);
v___x_1409_ = v_impl_1392_;
v_isShared_1410_ = v_isSharedCheck_1471_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_impl_1392_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1471_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_size_1411_; lean_object* v_k_1412_; lean_object* v_v_1413_; lean_object* v_l_1414_; lean_object* v_r_1415_; lean_object* v_size_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_size_1411_ = lean_ctor_get(v_l_1398_, 0);
v_k_1412_ = lean_ctor_get(v_l_1398_, 1);
v_v_1413_ = lean_ctor_get(v_l_1398_, 2);
v_l_1414_ = lean_ctor_get(v_l_1398_, 3);
v_r_1415_ = lean_ctor_get(v_l_1398_, 4);
v_size_1416_ = lean_ctor_get(v_r_1399_, 0);
v___x_1417_ = lean_unsigned_to_nat(2u);
v___x_1418_ = lean_nat_mul(v___x_1417_, v_size_1416_);
v___x_1419_ = lean_nat_dec_lt(v_size_1411_, v___x_1418_);
lean_dec(v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1447_; 
lean_inc(v_r_1415_);
lean_inc(v_l_1414_);
lean_inc(v_v_1413_);
lean_inc(v_k_1412_);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_l_1398_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_l_1398_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1398_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_l_1398_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1398_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1398_, 0);
lean_dec(v_unused_1452_);
v___x_1421_ = v_l_1398_;
v_isShared_1422_ = v_isSharedCheck_1447_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v_l_1398_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1447_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1437_; 
v___x_1423_ = lean_nat_add(v___x_1393_, v_size_1394_);
v___x_1424_ = lean_nat_add(v___x_1423_, v_size_1395_);
lean_dec(v_size_1395_);
if (lean_obj_tag(v_l_1414_) == 0)
{
lean_object* v_size_1445_; 
v_size_1445_ = lean_ctor_get(v_l_1414_, 0);
lean_inc(v_size_1445_);
v___y_1437_ = v_size_1445_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___y_1437_ = v___x_1446_;
goto v___jp_1436_;
}
v___jp_1425_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_nat_add(v___y_1426_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec(v___y_1426_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 4, v_r_1399_);
lean_ctor_set(v___x_1421_, 3, v_r_1415_);
lean_ctor_set(v___x_1421_, 2, v_v_1397_);
lean_ctor_set(v___x_1421_, 1, v_k_1396_);
lean_ctor_set(v___x_1421_, 0, v___x_1429_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_r_1415_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_r_1399_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1431_);
lean_ctor_set(v___x_1409_, 3, v___y_1427_);
lean_ctor_set(v___x_1409_, 2, v_v_1413_);
lean_ctor_set(v___x_1409_, 1, v_k_1412_);
lean_ctor_set(v___x_1409_, 0, v___x_1424_);
v___x_1433_ = v___x_1409_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1412_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1413_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___y_1427_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_nat_add(v___x_1423_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec(v___x_1423_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1414_);
lean_ctor_set(v___x_1386_, 0, v___x_1438_);
v___x_1440_ = v___x_1386_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_l_1414_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_nat_add(v___x_1393_, v_size_1416_);
if (lean_obj_tag(v_r_1415_) == 0)
{
lean_object* v_size_1442_; 
v_size_1442_ = lean_ctor_get(v_r_1415_, 0);
lean_inc(v_size_1442_);
v___y_1426_ = v___x_1441_;
v___y_1427_ = v___x_1440_;
v___y_1428_ = v_size_1442_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___y_1426_ = v___x_1441_;
v___y_1427_ = v___x_1440_;
v___y_1428_ = v___x_1443_;
goto v___jp_1425_;
}
}
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_del_object(v___x_1386_);
v___x_1453_ = lean_nat_add(v___x_1393_, v_size_1394_);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1395_);
lean_dec(v_size_1395_);
v___x_1455_ = lean_nat_add(v___x_1453_, v_size_1411_);
lean_dec(v___x_1453_);
lean_inc_ref(v_l_1383_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1398_);
lean_ctor_set(v___x_1409_, 3, v_l_1383_);
lean_ctor_set(v___x_1409_, 2, v_v_1382_);
lean_ctor_set(v___x_1409_, 1, v_k_1381_);
lean_ctor_set(v___x_1409_, 0, v___x_1455_);
v___x_1457_ = v___x_1409_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v_l_1398_);
v___x_1457_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v_l_1383_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1465_ = lean_ctor_get(v_l_1383_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_l_1383_, 3);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_l_1383_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_l_1383_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_l_1383_, 0);
lean_dec(v_unused_1469_);
v___x_1459_ = v_l_1383_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_l_1383_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v_r_1399_);
lean_ctor_set(v___x_1459_, 3, v___x_1457_);
lean_ctor_set(v___x_1459_, 2, v_v_1397_);
lean_ctor_set(v___x_1459_, 1, v_k_1396_);
lean_ctor_set(v___x_1459_, 0, v___x_1454_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_r_1399_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1477_; 
v_l_1477_ = lean_ctor_get(v_impl_1392_, 3);
lean_inc(v_l_1477_);
if (lean_obj_tag(v_l_1477_) == 0)
{
lean_object* v_r_1478_; lean_object* v_k_1479_; lean_object* v_v_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1503_; 
v_r_1478_ = lean_ctor_get(v_impl_1392_, 4);
v_k_1479_ = lean_ctor_get(v_impl_1392_, 1);
v_v_1480_ = lean_ctor_get(v_impl_1392_, 2);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_impl_1392_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1504_ = lean_ctor_get(v_impl_1392_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_impl_1392_, 0);
lean_dec(v_unused_1505_);
v___x_1482_ = v_impl_1392_;
v_isShared_1483_ = v_isSharedCheck_1503_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_r_1478_);
lean_inc(v_v_1480_);
lean_inc(v_k_1479_);
lean_dec(v_impl_1392_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1503_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1499_; 
v_k_1484_ = lean_ctor_get(v_l_1477_, 1);
v_v_1485_ = lean_ctor_get(v_l_1477_, 2);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_l_1477_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1500_ = lean_ctor_get(v_l_1477_, 4);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_l_1477_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_l_1477_, 0);
lean_dec(v_unused_1502_);
v___x_1487_ = v_l_1477_;
v_isShared_1488_ = v_isSharedCheck_1499_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_v_1485_);
lean_inc(v_k_1484_);
lean_dec(v_l_1477_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1499_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1478_, 2);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 4, v_r_1478_);
lean_ctor_set(v___x_1487_, 3, v_r_1478_);
lean_ctor_set(v___x_1487_, 2, v_v_1382_);
lean_ctor_set(v___x_1487_, 1, v_k_1381_);
lean_ctor_set(v___x_1487_, 0, v___x_1393_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_r_1478_);
v___x_1491_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
lean_inc(v_r_1478_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v_r_1478_);
lean_ctor_set(v___x_1482_, 0, v___x_1393_);
v___x_1493_ = v___x_1482_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1478_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1493_);
lean_ctor_set(v___x_1386_, 3, v___x_1491_);
lean_ctor_set(v___x_1386_, 2, v_v_1485_);
lean_ctor_set(v___x_1386_, 1, v_k_1484_);
lean_ctor_set(v___x_1386_, 0, v___x_1489_);
v___x_1495_ = v___x_1386_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_k_1484_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_v_1485_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
else
{
lean_object* v_r_1506_; 
v_r_1506_ = lean_ctor_get(v_impl_1392_, 4);
lean_inc(v_r_1506_);
if (lean_obj_tag(v_r_1506_) == 0)
{
lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1519_; 
v_k_1507_ = lean_ctor_get(v_impl_1392_, 1);
v_v_1508_ = lean_ctor_get(v_impl_1392_, 2);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_impl_1392_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; 
v_unused_1520_ = lean_ctor_get(v_impl_1392_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_impl_1392_, 3);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_impl_1392_, 0);
lean_dec(v_unused_1522_);
v___x_1510_ = v_impl_1392_;
v_isShared_1511_ = v_isSharedCheck_1519_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_v_1508_);
lean_inc(v_k_1507_);
lean_dec(v_impl_1392_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1519_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(3u);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_l_1477_);
lean_ctor_set(v___x_1510_, 2, v_v_1382_);
lean_ctor_set(v___x_1510_, 1, v_k_1381_);
lean_ctor_set(v___x_1510_, 0, v___x_1393_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1477_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_l_1477_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_r_1506_);
lean_ctor_set(v___x_1386_, 3, v___x_1514_);
lean_ctor_set(v___x_1386_, 2, v_v_1508_);
lean_ctor_set(v___x_1386_, 1, v_k_1507_);
lean_ctor_set(v___x_1386_, 0, v___x_1512_);
v___x_1516_ = v___x_1386_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1508_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1506_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(2u);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_impl_1392_);
lean_ctor_set(v___x_1386_, 3, v_r_1506_);
lean_ctor_set(v___x_1386_, 0, v___x_1523_);
v___x_1525_ = v___x_1386_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_r_1506_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_impl_1392_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
v___x_1527_ = lean_box_uint64(v_k_1377_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 2, v_v_1378_);
lean_ctor_set(v___x_1386_, 1, v___x_1527_);
v___x_1529_ = v___x_1386_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_size_1380_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1378_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1384_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_impl_1531_; lean_object* v___x_1532_; 
lean_dec(v_size_1380_);
v_impl_1531_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1377_, v_v_1378_, v_l_1383_);
v___x_1532_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1384_) == 0)
{
lean_object* v_size_1533_; lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v_l_1537_; lean_object* v_r_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_size_1533_ = lean_ctor_get(v_r_1384_, 0);
v_size_1534_ = lean_ctor_get(v_impl_1531_, 0);
v_k_1535_ = lean_ctor_get(v_impl_1531_, 1);
v_v_1536_ = lean_ctor_get(v_impl_1531_, 2);
v_l_1537_ = lean_ctor_get(v_impl_1531_, 3);
v_r_1538_ = lean_ctor_get(v_impl_1531_, 4);
lean_inc(v_r_1538_);
v___x_1539_ = lean_unsigned_to_nat(3u);
v___x_1540_ = lean_nat_mul(v___x_1539_, v_size_1533_);
v___x_1541_ = lean_nat_dec_lt(v___x_1540_, v_size_1534_);
lean_dec(v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_dec(v_r_1538_);
v___x_1542_ = lean_nat_add(v___x_1532_, v_size_1534_);
v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1533_);
lean_dec(v___x_1542_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 3, v_impl_1531_);
lean_ctor_set(v___x_1386_, 0, v___x_1543_);
v___x_1545_ = v___x_1386_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_impl_1531_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_r_1384_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1612_; 
lean_inc(v_l_1537_);
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_inc(v_size_1534_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_impl_1531_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v_impl_1531_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_impl_1531_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_impl_1531_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1531_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1531_, 0);
lean_dec(v_unused_1617_);
v___x_1548_ = v_impl_1531_;
v_isShared_1549_ = v_isSharedCheck_1612_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v_impl_1531_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1612_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_size_1550_; lean_object* v_size_1551_; lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v_l_1554_; lean_object* v_r_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_size_1550_ = lean_ctor_get(v_l_1537_, 0);
v_size_1551_ = lean_ctor_get(v_r_1538_, 0);
v_k_1552_ = lean_ctor_get(v_r_1538_, 1);
v_v_1553_ = lean_ctor_get(v_r_1538_, 2);
v_l_1554_ = lean_ctor_get(v_r_1538_, 3);
v_r_1555_ = lean_ctor_get(v_r_1538_, 4);
v___x_1556_ = lean_unsigned_to_nat(2u);
v___x_1557_ = lean_nat_mul(v___x_1556_, v_size_1550_);
v___x_1558_ = lean_nat_dec_lt(v_size_1551_, v___x_1557_);
lean_dec(v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1587_; 
lean_inc(v_r_1555_);
lean_inc(v_l_1554_);
lean_inc(v_v_1553_);
lean_inc(v_k_1552_);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_r_1538_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1588_ = lean_ctor_get(v_r_1538_, 4);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_r_1538_, 3);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_r_1538_, 2);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_r_1538_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_r_1538_, 0);
lean_dec(v_unused_1592_);
v___x_1560_ = v_r_1538_;
v_isShared_1561_ = v_isSharedCheck_1587_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v_r_1538_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1587_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___x_1575_; lean_object* v___y_1577_; 
v___x_1562_ = lean_nat_add(v___x_1532_, v_size_1534_);
lean_dec(v_size_1534_);
v___x_1563_ = lean_nat_add(v___x_1562_, v_size_1533_);
lean_dec(v___x_1562_);
v___x_1575_ = lean_nat_add(v___x_1532_, v_size_1550_);
if (lean_obj_tag(v_l_1554_) == 0)
{
lean_object* v_size_1585_; 
v_size_1585_ = lean_ctor_get(v_l_1554_, 0);
lean_inc(v_size_1585_);
v___y_1577_ = v_size_1585_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___y_1577_ = v___x_1586_;
goto v___jp_1576_;
}
v___jp_1564_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_nat_add(v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec(v___y_1566_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 4, v_r_1384_);
lean_ctor_set(v___x_1560_, 3, v_r_1555_);
lean_ctor_set(v___x_1560_, 2, v_v_1382_);
lean_ctor_set(v___x_1560_, 1, v_k_1381_);
lean_ctor_set(v___x_1560_, 0, v___x_1568_);
v___x_1570_ = v___x_1560_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_r_1555_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_r_1384_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v___x_1570_);
lean_ctor_set(v___x_1548_, 3, v___y_1565_);
lean_ctor_set(v___x_1548_, 2, v_v_1553_);
lean_ctor_set(v___x_1548_, 1, v_k_1552_);
lean_ctor_set(v___x_1548_, 0, v___x_1563_);
v___x_1572_ = v___x_1548_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v___y_1565_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
v___jp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = lean_nat_add(v___x_1575_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec(v___x_1575_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1554_);
lean_ctor_set(v___x_1386_, 3, v_l_1537_);
lean_ctor_set(v___x_1386_, 2, v_v_1536_);
lean_ctor_set(v___x_1386_, 1, v_k_1535_);
lean_ctor_set(v___x_1386_, 0, v___x_1578_);
v___x_1580_ = v___x_1386_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_l_1537_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_l_1554_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_nat_add(v___x_1532_, v_size_1533_);
if (lean_obj_tag(v_r_1555_) == 0)
{
lean_object* v_size_1582_; 
v_size_1582_ = lean_ctor_get(v_r_1555_, 0);
lean_inc(v_size_1582_);
v___y_1565_ = v___x_1580_;
v___y_1566_ = v___x_1581_;
v___y_1567_ = v_size_1582_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_unsigned_to_nat(0u);
v___y_1565_ = v___x_1580_;
v___y_1566_ = v___x_1581_;
v___y_1567_ = v___x_1583_;
goto v___jp_1564_;
}
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_del_object(v___x_1386_);
v___x_1593_ = lean_nat_add(v___x_1532_, v_size_1534_);
lean_dec(v_size_1534_);
v___x_1594_ = lean_nat_add(v___x_1593_, v_size_1533_);
lean_dec(v___x_1593_);
v___x_1595_ = lean_nat_add(v___x_1532_, v_size_1533_);
v___x_1596_ = lean_nat_add(v___x_1595_, v_size_1551_);
lean_dec(v___x_1595_);
lean_inc_ref(v_r_1384_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1384_);
lean_ctor_set(v___x_1548_, 3, v_r_1538_);
lean_ctor_set(v___x_1548_, 2, v_v_1382_);
lean_ctor_set(v___x_1548_, 1, v_k_1381_);
lean_ctor_set(v___x_1548_, 0, v___x_1596_);
v___x_1598_ = v___x_1548_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_r_1538_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_r_1384_);
v___x_1598_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v_r_1384_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1606_ = lean_ctor_get(v_r_1384_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1384_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_r_1384_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_r_1384_, 1);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_r_1384_, 0);
lean_dec(v_unused_1610_);
v___x_1600_ = v_r_1384_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_r_1384_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 4, v___x_1598_);
lean_ctor_set(v___x_1600_, 3, v_l_1537_);
lean_ctor_set(v___x_1600_, 2, v_v_1536_);
lean_ctor_set(v___x_1600_, 1, v_k_1535_);
lean_ctor_set(v___x_1600_, 0, v___x_1594_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_l_1537_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v___x_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1618_; 
v_l_1618_ = lean_ctor_get(v_impl_1531_, 3);
if (lean_obj_tag(v_l_1618_) == 0)
{
lean_object* v_r_1619_; lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1632_; 
lean_inc_ref(v_l_1618_);
v_r_1619_ = lean_ctor_get(v_impl_1531_, 4);
v_k_1620_ = lean_ctor_get(v_impl_1531_, 1);
v_v_1621_ = lean_ctor_get(v_impl_1531_, 2);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_impl_1531_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; lean_object* v_unused_1634_; 
v_unused_1633_ = lean_ctor_get(v_impl_1531_, 3);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_impl_1531_, 0);
lean_dec(v_unused_1634_);
v___x_1623_ = v_impl_1531_;
v_isShared_1624_ = v_isSharedCheck_1632_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_r_1619_);
lean_inc(v_v_1621_);
lean_inc(v_k_1620_);
lean_dec(v_impl_1531_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1632_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1619_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 3, v_r_1619_);
lean_ctor_set(v___x_1623_, 2, v_v_1382_);
lean_ctor_set(v___x_1623_, 1, v_k_1381_);
lean_ctor_set(v___x_1623_, 0, v___x_1532_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_r_1619_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_r_1619_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1627_);
lean_ctor_set(v___x_1386_, 3, v_l_1618_);
lean_ctor_set(v___x_1386_, 2, v_v_1621_);
lean_ctor_set(v___x_1386_, 1, v_k_1620_);
lean_ctor_set(v___x_1386_, 0, v___x_1625_);
v___x_1629_ = v___x_1386_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_l_1618_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_r_1635_; 
v_r_1635_ = lean_ctor_get(v_impl_1531_, 4);
lean_inc(v_r_1635_);
if (lean_obj_tag(v_r_1635_) == 0)
{
lean_object* v_k_1636_; lean_object* v_v_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1660_; 
lean_inc(v_l_1618_);
v_k_1636_ = lean_ctor_get(v_impl_1531_, 1);
v_v_1637_ = lean_ctor_get(v_impl_1531_, 2);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_impl_1531_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1661_ = lean_ctor_get(v_impl_1531_, 4);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_impl_1531_, 3);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_impl_1531_, 0);
lean_dec(v_unused_1663_);
v___x_1639_ = v_impl_1531_;
v_isShared_1640_ = v_isSharedCheck_1660_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_v_1637_);
lean_inc(v_k_1636_);
lean_dec(v_impl_1531_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1660_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_k_1641_; lean_object* v_v_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1656_; 
v_k_1641_ = lean_ctor_get(v_r_1635_, 1);
v_v_1642_ = lean_ctor_get(v_r_1635_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_r_1635_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; lean_object* v_unused_1659_; 
v_unused_1657_ = lean_ctor_get(v_r_1635_, 4);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_r_1635_, 3);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_r_1635_, 0);
lean_dec(v_unused_1659_);
v___x_1644_ = v_r_1635_;
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_v_1642_);
lean_inc(v_k_1641_);
lean_dec(v_r_1635_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(3u);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 4, v_l_1618_);
lean_ctor_set(v___x_1644_, 3, v_l_1618_);
lean_ctor_set(v___x_1644_, 2, v_v_1637_);
lean_ctor_set(v___x_1644_, 1, v_k_1636_);
lean_ctor_set(v___x_1644_, 0, v___x_1532_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1636_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1637_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_l_1618_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_l_1618_);
v___x_1648_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 4, v_l_1618_);
lean_ctor_set(v___x_1639_, 2, v_v_1382_);
lean_ctor_set(v___x_1639_, 1, v_k_1381_);
lean_ctor_set(v___x_1639_, 0, v___x_1532_);
v___x_1650_ = v___x_1639_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_l_1618_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_l_1618_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1650_);
lean_ctor_set(v___x_1386_, 3, v___x_1648_);
lean_ctor_set(v___x_1386_, 2, v_v_1642_);
lean_ctor_set(v___x_1386_, 1, v_k_1641_);
lean_ctor_set(v___x_1386_, 0, v___x_1646_);
v___x_1652_ = v___x_1386_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1641_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1642_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_unsigned_to_nat(2u);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_r_1635_);
lean_ctor_set(v___x_1386_, 3, v_impl_1531_);
lean_ctor_set(v___x_1386_, 0, v___x_1664_);
v___x_1666_ = v___x_1386_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_impl_1531_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_r_1635_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_box_uint64(v_k_1377_);
v___x_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
lean_ctor_set(v___x_1671_, 2, v_v_1378_);
lean_ctor_set(v___x_1671_, 3, v_t_1379_);
lean_ctor_set(v___x_1671_, 4, v_t_1379_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1672_, lean_object* v_v_1673_, lean_object* v_t_1674_){
_start:
{
uint64_t v_k_boxed_1675_; lean_object* v_res_1676_; 
v_k_boxed_1675_ = lean_unbox_uint64(v_k_1672_);
lean_dec_ref(v_k_1672_);
v_res_1676_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1675_, v_v_1673_, v_t_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1677_, lean_object* v_s_1678_){
_start:
{
uint64_t v_javascriptHash_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_javascriptHash_1679_ = lean_ctor_get_uint64(v_wi_1677_, sizeof(void*)*2);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_wi_1677_);
v___x_1681_ = lean_box(0);
v___x_1682_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1678_, v_javascriptHash_1679_, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1680_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1679_, v___x_1683_, v_s_1678_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v_env_1691_; lean_object* v_nextMacroScope_1692_; lean_object* v_ngen_1693_; lean_object* v_auxDeclNGen_1694_; lean_object* v_traceState_1695_; lean_object* v_recordedDeps_1696_; lean_object* v_messages_1697_; lean_object* v_infoState_1698_; lean_object* v_snapshotTasks_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1727_; 
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1689_, 0, v_wi_1685_);
v___x_1690_ = lean_st_ref_take(v___y_1687_);
v_env_1691_ = lean_ctor_get(v___x_1690_, 0);
v_nextMacroScope_1692_ = lean_ctor_get(v___x_1690_, 1);
v_ngen_1693_ = lean_ctor_get(v___x_1690_, 2);
v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1690_, 3);
v_traceState_1695_ = lean_ctor_get(v___x_1690_, 4);
v_recordedDeps_1696_ = lean_ctor_get(v___x_1690_, 6);
v_messages_1697_ = lean_ctor_get(v___x_1690_, 7);
v_infoState_1698_ = lean_ctor_get(v___x_1690_, 8);
v_snapshotTasks_1699_ = lean_ctor_get(v___x_1690_, 9);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1690_, 5);
lean_dec(v_unused_1728_);
v___x_1701_ = v___x_1690_;
v_isShared_1702_ = v_isSharedCheck_1727_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_snapshotTasks_1699_);
lean_inc(v_infoState_1698_);
lean_inc(v_messages_1697_);
lean_inc(v_recordedDeps_1696_);
lean_inc(v_traceState_1695_);
lean_inc(v_auxDeclNGen_1694_);
lean_inc(v_ngen_1693_);
lean_inc(v_nextMacroScope_1692_);
lean_inc(v_env_1691_);
lean_dec(v___x_1690_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1727_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1703_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1704_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1703_, v_env_1691_, v___f_1689_);
v___x_1705_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 5, v___x_1705_);
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1707_ = v___x_1701_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_nextMacroScope_1692_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_ngen_1693_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_auxDeclNGen_1694_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_traceState_1695_);
lean_ctor_set(v_reuseFailAlloc_1726_, 5, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1726_, 6, v_recordedDeps_1696_);
lean_ctor_set(v_reuseFailAlloc_1726_, 7, v_messages_1697_);
lean_ctor_set(v_reuseFailAlloc_1726_, 8, v_infoState_1698_);
lean_ctor_set(v_reuseFailAlloc_1726_, 9, v_snapshotTasks_1699_);
v___x_1707_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_mctx_1710_; lean_object* v_zetaDeltaFVarIds_1711_; lean_object* v_postponed_1712_; lean_object* v_diag_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1724_; 
v___x_1708_ = lean_st_ref_put(v___y_1687_, v___x_1707_);
v___x_1709_ = lean_st_ref_take(v___y_1686_);
v_mctx_1710_ = lean_ctor_get(v___x_1709_, 0);
v_zetaDeltaFVarIds_1711_ = lean_ctor_get(v___x_1709_, 2);
v_postponed_1712_ = lean_ctor_get(v___x_1709_, 3);
v_diag_1713_ = lean_ctor_get(v___x_1709_, 4);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___x_1709_, 1);
lean_dec(v_unused_1725_);
v___x_1715_ = v___x_1709_;
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_diag_1713_);
lean_inc(v_postponed_1712_);
lean_inc(v_zetaDeltaFVarIds_1711_);
lean_inc(v_mctx_1710_);
lean_dec(v___x_1709_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_mctx_1710_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_zetaDeltaFVarIds_1711_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_postponed_1712_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_diag_1713_);
v___x_1720_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_st_ref_put(v___y_1686_, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1717_);
return v___x_1722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec(v___y_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(lean_object* v_ext_1734_, lean_object* v_b_1735_, uint8_t v_kind_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_toCold_1741_; lean_object* v_currNamespace_1742_; lean_object* v___x_1743_; lean_object* v_env_1744_; lean_object* v_nextMacroScope_1745_; lean_object* v_ngen_1746_; lean_object* v_auxDeclNGen_1747_; lean_object* v_traceState_1748_; lean_object* v_recordedDeps_1749_; lean_object* v_messages_1750_; lean_object* v_infoState_1751_; lean_object* v_snapshotTasks_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1779_; 
v_toCold_1741_ = lean_ctor_get(v___y_1738_, 0);
v_currNamespace_1742_ = lean_ctor_get(v_toCold_1741_, 4);
v___x_1743_ = lean_st_ref_take(v___y_1739_);
v_env_1744_ = lean_ctor_get(v___x_1743_, 0);
v_nextMacroScope_1745_ = lean_ctor_get(v___x_1743_, 1);
v_ngen_1746_ = lean_ctor_get(v___x_1743_, 2);
v_auxDeclNGen_1747_ = lean_ctor_get(v___x_1743_, 3);
v_traceState_1748_ = lean_ctor_get(v___x_1743_, 4);
v_recordedDeps_1749_ = lean_ctor_get(v___x_1743_, 6);
v_messages_1750_ = lean_ctor_get(v___x_1743_, 7);
v_infoState_1751_ = lean_ctor_get(v___x_1743_, 8);
v_snapshotTasks_1752_ = lean_ctor_get(v___x_1743_, 9);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1743_, 5);
lean_dec(v_unused_1780_);
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1779_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snapshotTasks_1752_);
lean_inc(v_infoState_1751_);
lean_inc(v_messages_1750_);
lean_inc(v_recordedDeps_1749_);
lean_inc(v_traceState_1748_);
lean_inc(v_auxDeclNGen_1747_);
lean_inc(v_ngen_1746_);
lean_inc(v_nextMacroScope_1745_);
lean_inc(v_env_1744_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1779_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_inc(v_currNamespace_1742_);
v___x_1756_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1744_, v_ext_1734_, v_b_1735_, v_kind_1736_, v_currNamespace_1742_);
v___x_1757_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 5, v___x_1757_);
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_nextMacroScope_1745_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_ngen_1746_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_auxDeclNGen_1747_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_traceState_1748_);
lean_ctor_set(v_reuseFailAlloc_1778_, 5, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1778_, 6, v_recordedDeps_1749_);
lean_ctor_set(v_reuseFailAlloc_1778_, 7, v_messages_1750_);
lean_ctor_set(v_reuseFailAlloc_1778_, 8, v_infoState_1751_);
lean_ctor_set(v_reuseFailAlloc_1778_, 9, v_snapshotTasks_1752_);
v___x_1759_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_mctx_1762_; lean_object* v_zetaDeltaFVarIds_1763_; lean_object* v_postponed_1764_; lean_object* v_diag_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1776_; 
v___x_1760_ = lean_st_ref_put(v___y_1739_, v___x_1759_);
v___x_1761_ = lean_st_ref_take(v___y_1737_);
v_mctx_1762_ = lean_ctor_get(v___x_1761_, 0);
v_zetaDeltaFVarIds_1763_ = lean_ctor_get(v___x_1761_, 2);
v_postponed_1764_ = lean_ctor_get(v___x_1761_, 3);
v_diag_1765_ = lean_ctor_get(v___x_1761_, 4);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1761_, 1);
lean_dec(v_unused_1777_);
v___x_1767_ = v___x_1761_;
v_isShared_1768_ = v_isSharedCheck_1776_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_diag_1765_);
lean_inc(v_postponed_1764_);
lean_inc(v_zetaDeltaFVarIds_1763_);
lean_inc(v_mctx_1762_);
lean_dec(v___x_1761_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1776_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_mctx_1762_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_zetaDeltaFVarIds_1763_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_postponed_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_diag_1765_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_st_ref_put(v___y_1737_, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1769_);
return v___x_1774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg___boxed(lean_object* v_ext_1781_, lean_object* v_b_1782_, lean_object* v_kind_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
uint8_t v_kind_boxed_1788_; lean_object* v_res_1789_; 
v_kind_boxed_1788_ = lean_unbox(v_kind_1783_);
v_res_1789_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v_ext_1781_, v_b_1782_, v_kind_boxed_1788_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1790_, lean_object* v_n_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1799_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1800_ = lean_box_uint64(v_h_1790_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_n_1791_);
v___x_1802_ = 2;
v___x_1803_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v___x_1799_, v___x_1801_, v___x_1802_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1804_, lean_object* v_n_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
uint64_t v_h_boxed_1813_; lean_object* v_res_1814_; 
v_h_boxed_1813_ = lean_unbox_uint64(v_h_1804_);
lean_dec_ref(v_h_1804_);
v_res_1814_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1813_, v_n_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1815_, lean_object* v_n_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1824_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1825_ = lean_box_uint64(v_h_1815_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v_n_1816_);
v___x_1827_ = 0;
v___x_1828_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v___x_1824_, v___x_1826_, v___x_1827_, v___y_1820_, v___y_1821_, v___y_1822_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1829_, lean_object* v_n_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint64_t v_h_boxed_1838_; lean_object* v_res_1839_; 
v_h_boxed_1838_ = lean_unbox_uint64(v_h_1829_);
lean_dec_ref(v_h_1829_);
v_res_1839_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1838_, v_n_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_1840_, lean_object* v___y_1841_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v_x_1840_, 0);
lean_inc(v_a_1842_);
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1842_);
lean_ctor_set(v___x_1843_, 1, v___y_1841_);
return v___x_1843_;
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v_x_1840_, 0);
lean_inc(v_a_1844_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1844_);
lean_ctor_set(v___x_1845_, 1, v___y_1841_);
return v___x_1845_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_1846_, v___y_1847_);
lean_dec_ref(v_x_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1849_, lean_object* v_stx_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1849_, v_stx_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
if (lean_obj_tag(v_a_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
v_a_1855_ = lean_ctor_get(v___x_1853_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1853_, 0);
lean_dec(v_unused_1864_);
v___x_1857_ = v___x_1853_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_box(0);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_a_1855_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v_val_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1893_; 
v_val_1865_ = lean_ctor_get(v_a_1854_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_a_1854_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1867_ = v_a_1854_;
v_isShared_1868_ = v_isSharedCheck_1893_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_val_1865_);
lean_dec(v_a_1854_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1893_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_snd_1869_; 
v_snd_1869_ = lean_ctor_get(v_val_1865_, 1);
lean_inc(v_snd_1869_);
lean_dec(v_val_1865_);
if (lean_obj_tag(v_snd_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1879_; 
lean_del_object(v___x_1867_);
v_a_1870_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1853_, 2);
v_a_1871_ = lean_ctor_get(v_snd_1869_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_snd_1869_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1873_ = v_snd_1869_;
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v_snd_1869_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1876_, v_a_1870_);
lean_dec_ref(v___x_1876_);
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1892_; 
v_a_1880_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1853_, 2);
v_a_1881_ = lean_ctor_get(v_snd_1869_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_snd_1869_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1883_ = v_snd_1869_;
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v_snd_1869_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_a_1881_);
v___x_1886_ = v___x_1867_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1888_, v_a_1880_);
lean_dec_ref(v___x_1888_);
return v___x_1889_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1894_ = lean_ctor_get(v___x_1853_, 0);
v_a_1895_ = lean_ctor_get(v___x_1853_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1853_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_inc(v_a_1894_);
lean_dec(v___x_1853_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1903_, lean_object* v_stx_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1903_, v_stx_1904_, v___y_1905_, v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; lean_object* v_env_1915_; uint8_t v___x_1916_; lean_object* v_env_1917_; lean_object* v___x_1918_; lean_object* v_toCold_1919_; lean_object* v_mctx_1920_; lean_object* v_lctx_1921_; lean_object* v_options_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1914_ = lean_st_ref_get(v___y_1912_);
v_env_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_env_1915_);
lean_dec(v___x_1914_);
v___x_1916_ = 0;
v_env_1917_ = l_Lean_Environment_setRecordingDeps(v_env_1915_, v___x_1916_);
v___x_1918_ = lean_st_ref_get(v___y_1910_);
v_toCold_1919_ = lean_ctor_get(v___y_1911_, 0);
v_mctx_1920_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_ref(v_mctx_1920_);
lean_dec(v___x_1918_);
v_lctx_1921_ = lean_ctor_get(v___y_1909_, 2);
v_options_1922_ = lean_ctor_get(v_toCold_1919_, 2);
lean_inc_ref(v_options_1922_);
lean_inc_ref(v_lctx_1921_);
v___x_1923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1923_, 0, v_env_1917_);
lean_ctor_set(v___x_1923_, 1, v_mctx_1920_);
lean_ctor_set(v___x_1923_, 2, v_lctx_1921_);
lean_ctor_set(v___x_1923_, 3, v_options_1922_);
v___x_1924_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_msgData_1908_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1933_; double v___x_1934_; 
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_float_of_nat(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1937_, lean_object* v_msg_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_ref_1944_; lean_object* v___x_1945_; lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1991_; 
v_ref_1944_ = lean_ctor_get(v___y_1941_, 2);
v___x_1945_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msg_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1991_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1991_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v_traceState_1951_; lean_object* v_env_1952_; lean_object* v_nextMacroScope_1953_; lean_object* v_ngen_1954_; lean_object* v_auxDeclNGen_1955_; lean_object* v_cache_1956_; lean_object* v_recordedDeps_1957_; lean_object* v_messages_1958_; lean_object* v_infoState_1959_; lean_object* v_snapshotTasks_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1990_; 
v___x_1950_ = lean_st_ref_take(v___y_1942_);
v_traceState_1951_ = lean_ctor_get(v___x_1950_, 4);
v_env_1952_ = lean_ctor_get(v___x_1950_, 0);
v_nextMacroScope_1953_ = lean_ctor_get(v___x_1950_, 1);
v_ngen_1954_ = lean_ctor_get(v___x_1950_, 2);
v_auxDeclNGen_1955_ = lean_ctor_get(v___x_1950_, 3);
v_cache_1956_ = lean_ctor_get(v___x_1950_, 5);
v_recordedDeps_1957_ = lean_ctor_get(v___x_1950_, 6);
v_messages_1958_ = lean_ctor_get(v___x_1950_, 7);
v_infoState_1959_ = lean_ctor_get(v___x_1950_, 8);
v_snapshotTasks_1960_ = lean_ctor_get(v___x_1950_, 9);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1962_ = v___x_1950_;
v_isShared_1963_ = v_isSharedCheck_1990_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snapshotTasks_1960_);
lean_inc(v_infoState_1959_);
lean_inc(v_messages_1958_);
lean_inc(v_recordedDeps_1957_);
lean_inc(v_cache_1956_);
lean_inc(v_traceState_1951_);
lean_inc(v_auxDeclNGen_1955_);
lean_inc(v_ngen_1954_);
lean_inc(v_nextMacroScope_1953_);
lean_inc(v_env_1952_);
lean_dec(v___x_1950_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1990_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
uint64_t v_tid_1964_; lean_object* v_traces_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1989_; 
v_tid_1964_ = lean_ctor_get_uint64(v_traceState_1951_, sizeof(void*)*1);
v_traces_1965_ = lean_ctor_get(v_traceState_1951_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_traceState_1951_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1967_ = v_traceState_1951_;
v_isShared_1968_ = v_isSharedCheck_1989_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_traces_1965_);
lean_dec(v_traceState_1951_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1989_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; double v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1972_ = 0;
v___x_1973_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1974_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1974_, 0, v_cls_1937_);
lean_ctor_set(v___x_1974_, 1, v___x_1970_);
lean_ctor_set(v___x_1974_, 2, v___x_1973_);
lean_ctor_set_float(v___x_1974_, sizeof(void*)*3, v___x_1971_);
lean_ctor_set_float(v___x_1974_, sizeof(void*)*3 + 8, v___x_1971_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*3 + 16, v___x_1972_);
v___x_1975_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1976_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v_a_1946_);
lean_ctor_set(v___x_1976_, 2, v___x_1975_);
lean_inc(v_ref_1944_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v_ref_1944_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_PersistentArray_push___redArg(v_traces_1965_, v___x_1977_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1978_);
v___x_1980_ = v___x_1967_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1978_);
lean_ctor_set_uint64(v_reuseFailAlloc_1988_, sizeof(void*)*1, v_tid_1964_);
v___x_1980_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v___x_1980_);
v___x_1982_ = v___x_1962_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_env_1952_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_nextMacroScope_1953_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_ngen_1954_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_auxDeclNGen_1955_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 5, v_cache_1956_);
lean_ctor_set(v_reuseFailAlloc_1987_, 6, v_recordedDeps_1957_);
lean_ctor_set(v_reuseFailAlloc_1987_, 7, v_messages_1958_);
lean_ctor_set(v_reuseFailAlloc_1987_, 8, v_infoState_1959_);
lean_ctor_set(v_reuseFailAlloc_1987_, 9, v_snapshotTasks_1960_);
v___x_1982_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_st_ref_put(v___y_1942_, v___x_1982_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1969_);
v___x_1985_ = v___x_1948_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1969_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1992_, lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1992_, v_msg_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
if (lean_obj_tag(v_as_2003_) == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_box(0);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
return v___x_2012_;
}
else
{
lean_object* v_toCold_2013_; lean_object* v_options_2014_; uint8_t v_hasTrace_2015_; 
v_toCold_2013_ = lean_ctor_get(v___y_2008_, 0);
v_options_2014_ = lean_ctor_get(v_toCold_2013_, 2);
v_hasTrace_2015_ = lean_ctor_get_uint8(v_options_2014_, sizeof(void*)*1);
if (v_hasTrace_2015_ == 0)
{
lean_object* v_tail_2016_; 
v_tail_2016_ = lean_ctor_get(v_as_2003_, 1);
lean_inc(v_tail_2016_);
lean_dec_ref_known(v_as_2003_, 2);
v_as_2003_ = v_tail_2016_;
goto _start;
}
else
{
lean_object* v_head_2018_; lean_object* v_tail_2019_; lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v_inheritedTraceOptions_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_head_2018_ = lean_ctor_get(v_as_2003_, 0);
lean_inc(v_head_2018_);
v_tail_2019_ = lean_ctor_get(v_as_2003_, 1);
lean_inc(v_tail_2019_);
lean_dec_ref_known(v_as_2003_, 2);
v_fst_2020_ = lean_ctor_get(v_head_2018_, 0);
lean_inc_n(v_fst_2020_, 2);
v_snd_2021_ = lean_ctor_get(v_head_2018_, 1);
lean_inc(v_snd_2021_);
lean_dec(v_head_2018_);
v_inheritedTraceOptions_2022_ = lean_ctor_get(v_toCold_2013_, 11);
v___x_2023_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2024_ = l_Lean_Name_append(v___x_2023_, v_fst_2020_);
v___x_2025_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2022_, v_options_2014_, v___x_2024_);
lean_dec(v___x_2024_);
if (v___x_2025_ == 0)
{
lean_dec(v_snd_2021_);
lean_dec(v_fst_2020_);
v_as_2003_ = v_tail_2019_;
goto _start;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_snd_2021_);
v___x_2028_ = l_Lean_MessageData_ofFormat(v___x_2027_);
v___x_2029_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_2020_, v___x_2028_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref_known(v___x_2029_, 1);
v_as_2003_ = v_tail_2019_;
goto _start;
}
else
{
lean_dec(v_tail_2019_);
return v___x_2029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_currNamespace_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_currNamespace_2040_);
lean_ctor_set(v___x_2043_, 1, v___y_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_currNamespace_2044_, v___y_2045_, v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2047_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(lean_object* v_opts_2048_, lean_object* v_opt_2049_){
_start:
{
lean_object* v_name_2050_; lean_object* v_defValue_2051_; lean_object* v_map_2052_; lean_object* v___x_2053_; 
v_name_2050_ = lean_ctor_get(v_opt_2049_, 0);
v_defValue_2051_ = lean_ctor_get(v_opt_2049_, 1);
v_map_2052_ = lean_ctor_get(v_opts_2048_, 0);
v___x_2053_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2052_, v_name_2050_);
if (lean_obj_tag(v___x_2053_) == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_unbox(v_defValue_2051_);
return v___x_2054_;
}
else
{
lean_object* v_val_2055_; 
v_val_2055_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_val_2055_);
lean_dec_ref_known(v___x_2053_, 1);
if (lean_obj_tag(v_val_2055_) == 1)
{
uint8_t v_v_2056_; 
v_v_2056_ = lean_ctor_get_uint8(v_val_2055_, 0);
lean_dec_ref_known(v_val_2055_, 0);
return v_v_2056_;
}
else
{
uint8_t v___x_2057_; 
lean_dec(v_val_2055_);
v___x_2057_ = lean_unbox(v_defValue_2051_);
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___boxed(lean_object* v_opts_2058_, lean_object* v_opt_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(v_opts_2058_, v_opt_2059_);
lean_dec_ref(v_opt_2059_);
lean_dec_ref(v_opts_2058_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_box(1);
v___x_2063_ = l_Lean_MessageData_ofFormat(v___x_2062_);
return v___x_2063_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__2));
v___x_2068_ = l_Lean_MessageData_ofFormat(v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
return v_x_2069_;
}
else
{
lean_object* v_head_2071_; lean_object* v_tail_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2094_; 
v_head_2071_ = lean_ctor_get(v_x_2070_, 0);
v_tail_2072_ = lean_ctor_get(v_x_2070_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_2070_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2074_ = v_x_2070_;
v_isShared_2075_ = v_isSharedCheck_2094_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tail_2072_);
lean_inc(v_head_2071_);
lean_dec(v_x_2070_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2094_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_before_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2092_; 
v_before_2076_ = lean_ctor_get(v_head_2071_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_head_2071_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v_head_2071_, 1);
lean_dec(v_unused_2093_);
v___x_2078_ = v_head_2071_;
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_before_2076_);
lean_dec(v_head_2071_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 7);
lean_ctor_set(v___x_2078_, 1, v___x_2080_);
lean_ctor_set(v___x_2078_, 0, v_x_2069_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_x_2069_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 7);
lean_ctor_set(v___x_2074_, 1, v___x_2083_);
lean_ctor_set(v___x_2074_, 0, v___x_2082_);
v___x_2085_ = v___x_2074_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_MessageData_ofSyntax(v_before_2076_);
v___x_2087_ = l_Lean_indentD(v___x_2086_);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2085_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v_x_2069_ = v___x_2088_;
v_x_2070_ = v_tail_2072_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__1));
v___x_2099_ = l_Lean_MessageData_ofFormat(v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(lean_object* v_msgData_2100_, lean_object* v_macroStack_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2102_);
v___x_2105_ = l_Lean_Elab_pp_macroStack;
v___x_2106_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(v___x_2104_, v___x_2105_);
lean_dec_ref(v___x_2104_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec(v_macroStack_2101_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_msgData_2100_);
return v___x_2107_;
}
else
{
if (lean_obj_tag(v_macroStack_2101_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_msgData_2100_);
return v___x_2108_;
}
else
{
lean_object* v_head_2109_; lean_object* v_after_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2125_; 
v_head_2109_ = lean_ctor_get(v_macroStack_2101_, 0);
lean_inc(v_head_2109_);
v_after_2110_ = lean_ctor_get(v_head_2109_, 1);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_head_2109_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v_head_2109_, 0);
lean_dec(v_unused_2126_);
v___x_2112_ = v_head_2109_;
v_isShared_2113_ = v_isSharedCheck_2125_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_after_2110_);
lean_dec(v_head_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2125_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 7);
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
lean_ctor_set(v___x_2112_, 0, v_msgData_2100_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_msgData_2100_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_msgData_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2117_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = l_Lean_MessageData_ofSyntax(v_after_2110_);
v___x_2120_ = l_Lean_indentD(v___x_2119_);
v_msgData_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2121_, 0, v___x_2118_);
lean_ctor_set(v_msgData_2121_, 1, v___x_2120_);
v___x_2122_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24(v_msgData_2121_, v_macroStack_2101_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___boxed(lean_object* v_msgData_2127_, lean_object* v_macroStack_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_msgData_2127_, v_macroStack_2128_, v___y_2129_);
lean_dec_ref(v___y_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_ref_2140_; lean_object* v_macroStack_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2154_; 
v_ref_2140_ = lean_ctor_get(v___y_2137_, 2);
v_macroStack_2141_ = lean_ctor_get(v___y_2133_, 1);
v___x_2142_ = l_Lean_Elab_getBetterRef(v_ref_2140_, v_macroStack_2141_);
v___x_2143_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msg_2132_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
lean_inc(v_macroStack_2141_);
v___x_2145_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_a_2144_, v_macroStack_2141_, v___y_2137_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2142_);
lean_ctor_set(v___x_2150_, 1, v_a_2146_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set_tag(v___x_2148_, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2164_, lean_object* v_msg_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_toCold_2173_; lean_object* v_currRecDepth_2174_; lean_object* v_ref_2175_; uint16_t v_optionFlags_2176_; uint8_t v_suppressElabErrors_2177_; uint8_t v_checkDeprecated_2178_; uint8_t v_isRecordingDeps_2179_; lean_object* v_ref_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_toCold_2173_ = lean_ctor_get(v___y_2170_, 0);
v_currRecDepth_2174_ = lean_ctor_get(v___y_2170_, 1);
v_ref_2175_ = lean_ctor_get(v___y_2170_, 2);
v_optionFlags_2176_ = lean_ctor_get_uint16(v___y_2170_, sizeof(void*)*3);
v_suppressElabErrors_2177_ = lean_ctor_get_uint8(v___y_2170_, sizeof(void*)*3 + 2);
v_checkDeprecated_2178_ = lean_ctor_get_uint8(v___y_2170_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2179_ = lean_ctor_get_uint8(v___y_2170_, sizeof(void*)*3 + 4);
v_ref_2180_ = l_Lean_replaceRef(v_ref_2164_, v_ref_2175_);
lean_inc(v_currRecDepth_2174_);
lean_inc_ref(v_toCold_2173_);
v___x_2181_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2181_, 0, v_toCold_2173_);
lean_ctor_set(v___x_2181_, 1, v_currRecDepth_2174_);
lean_ctor_set(v___x_2181_, 2, v_ref_2180_);
lean_ctor_set_uint16(v___x_2181_, sizeof(void*)*3, v_optionFlags_2176_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*3 + 2, v_suppressElabErrors_2177_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*3 + 3, v_checkDeprecated_2178_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*3 + 4, v_isRecordingDeps_2179_);
v___x_2182_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___x_2181_, v___y_2171_);
lean_dec_ref_known(v___x_2181_, 3);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2183_, lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v_ref_2183_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2193_, lean_object* v_currNamespace_2194_, lean_object* v_openDecls_2195_, lean_object* v_n_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = l_Lean_ResolveName_resolveNamespace(v_env_2193_, v_currNamespace_2194_, v_openDecls_2195_, v_n_2196_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2201_, lean_object* v_currNamespace_2202_, lean_object* v_openDecls_2203_, lean_object* v_n_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2201_, v_currNamespace_2202_, v_openDecls_2203_, v_n_2204_, v___y_2205_, v___y_2206_);
lean_dec_ref(v___y_2205_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0(lean_object* v___x_2208_, lean_object* v_entry_2209_, lean_object* v_s_2210_){
_start:
{
lean_object* v_addEntryFn_2211_; lean_object* v_importedEntries_2212_; lean_object* v_state_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2221_; 
v_addEntryFn_2211_ = lean_ctor_get(v___x_2208_, 3);
lean_inc(v_addEntryFn_2211_);
lean_dec_ref(v___x_2208_);
v_importedEntries_2212_ = lean_ctor_get(v_s_2210_, 0);
v_state_2213_ = lean_ctor_get(v_s_2210_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_s_2210_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2215_ = v_s_2210_;
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_state_2213_);
lean_inc(v_importedEntries_2212_);
lean_dec(v_s_2210_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_state_2217_; lean_object* v___x_2219_; 
v_state_2217_ = lean_apply_2(v_addEntryFn_2211_, v_state_2213_, v_entry_2209_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v_state_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_importedEntries_2212_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_state_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(lean_object* v_keys_2222_, lean_object* v_i_2223_, lean_object* v_k_2224_){
_start:
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_array_get_size(v_keys_2222_);
v___x_2226_ = lean_nat_dec_lt(v_i_2223_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_dec(v_i_2223_);
return v___x_2226_;
}
else
{
lean_object* v_k_x27_2227_; uint8_t v___x_2228_; 
v_k_x27_2227_ = lean_array_fget_borrowed(v_keys_2222_, v_i_2223_);
v___x_2228_ = l_Lean_instBEqExtraModUse_beq(v_k_2224_, v_k_x27_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_add(v_i_2223_, v___x_2229_);
lean_dec(v_i_2223_);
v_i_2223_ = v___x_2230_;
goto _start;
}
else
{
lean_dec(v_i_2223_);
return v___x_2226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg___boxed(lean_object* v_keys_2232_, lean_object* v_i_2233_, lean_object* v_k_2234_){
_start:
{
uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_res_2235_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(v_keys_2232_, v_i_2233_, v_k_2234_);
lean_dec_ref(v_k_2234_);
lean_dec_ref(v_keys_2232_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(lean_object* v_x_2237_, size_t v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2237_) == 0)
{
lean_object* v_es_2240_; lean_object* v___x_2241_; size_t v___x_2242_; size_t v___x_2243_; lean_object* v_j_2244_; lean_object* v___x_2245_; 
v_es_2240_ = lean_ctor_get(v_x_2237_, 0);
v___x_2241_ = lean_box(2);
v___x_2242_ = ((size_t)31ULL);
v___x_2243_ = lean_usize_land(v_x_2238_, v___x_2242_);
v_j_2244_ = lean_usize_to_nat(v___x_2243_);
v___x_2245_ = lean_array_get_borrowed(v___x_2241_, v_es_2240_, v_j_2244_);
lean_dec(v_j_2244_);
switch(lean_obj_tag(v___x_2245_))
{
case 0:
{
lean_object* v_key_2246_; uint8_t v___x_2247_; 
v_key_2246_ = lean_ctor_get(v___x_2245_, 0);
v___x_2247_ = l_Lean_instBEqExtraModUse_beq(v_x_2239_, v_key_2246_);
return v___x_2247_;
}
case 1:
{
lean_object* v_node_2248_; size_t v___x_2249_; size_t v___x_2250_; 
v_node_2248_ = lean_ctor_get(v___x_2245_, 0);
v___x_2249_ = ((size_t)5ULL);
v___x_2250_ = lean_usize_shift_right(v_x_2238_, v___x_2249_);
v_x_2237_ = v_node_2248_;
v_x_2238_ = v___x_2250_;
goto _start;
}
default: 
{
uint8_t v___x_2252_; 
v___x_2252_ = 0;
return v___x_2252_;
}
}
}
else
{
lean_object* v_ks_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_ks_2253_ = lean_ctor_get(v_x_2237_, 0);
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(v_ks_2253_, v___x_2254_, v_x_2239_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg___boxed(lean_object* v_x_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
size_t v_x_30286__boxed_2259_; uint8_t v_res_2260_; lean_object* v_r_2261_; 
v_x_30286__boxed_2259_ = lean_unbox_usize(v_x_2257_);
lean_dec(v_x_2257_);
v_res_2260_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(v_x_2256_, v_x_30286__boxed_2259_, v_x_2258_);
lean_dec_ref(v_x_2258_);
lean_dec_ref(v_x_2256_);
v_r_2261_ = lean_box(v_res_2260_);
return v_r_2261_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(lean_object* v_x_2262_, lean_object* v_x_2263_){
_start:
{
uint64_t v___x_2264_; size_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2264_ = l_Lean_instHashableExtraModUse_hash(v_x_2263_);
v___x_2265_ = lean_uint64_to_usize(v___x_2264_);
v___x_2266_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(v_x_2262_, v___x_2265_, v_x_2263_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg___boxed(lean_object* v_x_2267_, lean_object* v_x_2268_){
_start:
{
uint8_t v_res_2269_; lean_object* v_r_2270_; 
v_res_2269_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(v_x_2267_, v_x_2268_);
lean_dec_ref(v_x_2268_);
lean_dec_ref(v_x_2267_);
v_r_2270_ = lean_box(v_res_2269_);
return v_r_2270_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2271_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v_cls_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_cls_2283_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2284_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2285_ = l_Lean_Name_append(v___x_2284_, v_cls_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2296_, uint8_t v_isMeta_2297_, lean_object* v_hint_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v_env_2340_; uint8_t v_isExporting_2341_; lean_object* v_entry_2342_; lean_object* v___x_2343_; lean_object* v_env_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2338_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0);
v___x_2339_ = lean_st_ref_get(v___y_2304_);
v_env_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc_ref(v_env_2340_);
lean_dec(v___x_2339_);
v_isExporting_2341_ = lean_ctor_get_uint8(v_env_2340_, sizeof(void*)*13);
lean_dec_ref(v_env_2340_);
lean_inc(v_mod_2296_);
v_entry_2342_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2342_, 0, v_mod_2296_);
lean_ctor_set_uint8(v_entry_2342_, sizeof(void*)*1, v_isExporting_2341_);
lean_ctor_set_uint8(v_entry_2342_, sizeof(void*)*1 + 1, v_isMeta_2297_);
v___x_2343_ = lean_st_ref_get(v___y_2304_);
v_env_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc_ref(v_env_2344_);
lean_dec(v___x_2343_);
v___x_2345_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2346_ = lean_box(1);
v___x_2347_ = lean_box(0);
v___x_2348_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2338_, v___x_2345_, v_env_2344_, v___x_2346_, v___x_2347_);
v___x_2349_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(v___x_2348_, v_entry_2342_);
lean_dec(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v_toCold_2350_; lean_object* v_options_2351_; lean_object* v_inheritedTraceOptions_2352_; uint8_t v_hasTrace_2353_; lean_object* v___f_2354_; uint8_t v___x_2355_; lean_object* v___y_2357_; lean_object* v___y_2358_; 
v_toCold_2350_ = lean_ctor_get(v___y_2303_, 0);
v_options_2351_ = lean_ctor_get(v_toCold_2350_, 2);
v_inheritedTraceOptions_2352_ = lean_ctor_get(v_toCold_2350_, 11);
v_hasTrace_2353_ = lean_ctor_get_uint8(v_options_2351_, sizeof(void*)*1);
v___f_2354_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_2354_, 0, v___x_2345_);
lean_closure_set(v___f_2354_, 1, v_entry_2342_);
v___x_2355_ = 1;
if (v_hasTrace_2353_ == 0)
{
lean_dec(v_hint_2298_);
lean_dec(v_mod_2296_);
v___y_2357_ = v___y_2302_;
v___y_2358_ = v___y_2304_;
goto v___jp_2356_;
}
else
{
lean_object* v_cls_2385_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_cls_2385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2405_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2406_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2352_, v_options_2351_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec(v_hint_2298_);
lean_dec(v_mod_2296_);
v___y_2357_ = v___y_2302_;
v___y_2358_ = v___y_2304_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2407_; lean_object* v___y_2409_; 
v___x_2407_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
if (v_isExporting_2341_ == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2409_ = v___x_2416_;
goto v___jp_2408_;
}
else
{
lean_object* v___x_2417_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2409_ = v___x_2417_;
goto v___jp_2408_;
}
v___jp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_inc_ref(v___y_2409_);
v___x_2410_ = l_Lean_stringToMessageData(v___y_2409_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2407_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
if (v_isMeta_2297_ == 0)
{
lean_object* v___x_2414_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___y_2392_ = v___x_2413_;
v___y_2393_ = v___x_2414_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2415_; 
v___x_2415_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14));
v___y_2392_ = v___x_2413_;
v___y_2393_ = v___x_2415_;
goto v___jp_2391_;
}
}
}
v___jp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___y_2387_);
lean_ctor_set(v___x_2389_, 1, v___y_2388_);
v___x_2390_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2385_, v___x_2389_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_dec_ref_known(v___x_2390_, 1);
v___y_2357_ = v___y_2302_;
v___y_2358_ = v___y_2304_;
goto v___jp_2356_;
}
else
{
lean_dec_ref(v___f_2354_);
return v___x_2390_;
}
}
v___jp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
lean_inc_ref(v___y_2393_);
v___x_2394_ = l_Lean_stringToMessageData(v___y_2393_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___y_2392_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = l_Lean_MessageData_ofName(v_mod_2296_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_Name_isAnonymous(v_hint_2298_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2402_ = l_Lean_MessageData_ofName(v_hint_2298_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___y_2387_ = v___x_2399_;
v___y_2388_ = v___x_2403_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2404_; 
lean_dec(v_hint_2298_);
v___x_2404_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7);
v___y_2387_ = v___x_2399_;
v___y_2388_ = v___x_2404_;
goto v___jp_2386_;
}
}
}
v___jp_2356_:
{
lean_object* v___x_2359_; lean_object* v_toEnvExtension_2360_; uint8_t v_logWrites_2361_; 
v___x_2359_ = lean_st_ref_take(v___y_2358_);
v_toEnvExtension_2360_ = lean_ctor_get(v___x_2345_, 0);
v_logWrites_2361_ = lean_ctor_get_uint8(v_toEnvExtension_2360_, sizeof(void*)*6);
if (v_logWrites_2361_ == 0)
{
lean_object* v_env_2362_; lean_object* v_nextMacroScope_2363_; lean_object* v_ngen_2364_; lean_object* v_auxDeclNGen_2365_; lean_object* v_traceState_2366_; lean_object* v_recordedDeps_2367_; lean_object* v_messages_2368_; lean_object* v_infoState_2369_; lean_object* v_snapshotTasks_2370_; lean_object* v_asyncMode_2371_; lean_object* v___x_2372_; 
v_env_2362_ = lean_ctor_get(v___x_2359_, 0);
lean_inc_ref(v_env_2362_);
v_nextMacroScope_2363_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_nextMacroScope_2363_);
v_ngen_2364_ = lean_ctor_get(v___x_2359_, 2);
lean_inc_ref(v_ngen_2364_);
v_auxDeclNGen_2365_ = lean_ctor_get(v___x_2359_, 3);
lean_inc_ref(v_auxDeclNGen_2365_);
v_traceState_2366_ = lean_ctor_get(v___x_2359_, 4);
lean_inc_ref(v_traceState_2366_);
v_recordedDeps_2367_ = lean_ctor_get(v___x_2359_, 6);
lean_inc_ref(v_recordedDeps_2367_);
v_messages_2368_ = lean_ctor_get(v___x_2359_, 7);
lean_inc_ref(v_messages_2368_);
v_infoState_2369_ = lean_ctor_get(v___x_2359_, 8);
lean_inc_ref(v_infoState_2369_);
v_snapshotTasks_2370_ = lean_ctor_get(v___x_2359_, 9);
lean_inc_ref(v_snapshotTasks_2370_);
lean_dec(v___x_2359_);
v_asyncMode_2371_ = lean_ctor_get(v_toEnvExtension_2360_, 2);
lean_inc_ref(v_toEnvExtension_2360_);
v___x_2372_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2360_, v_env_2362_, v___f_2354_, v_asyncMode_2371_, v___x_2347_, v___x_2355_);
v___y_2307_ = v_traceState_2366_;
v___y_2308_ = v_infoState_2369_;
v___y_2309_ = v_messages_2368_;
v___y_2310_ = v_nextMacroScope_2363_;
v___y_2311_ = v_ngen_2364_;
v___y_2312_ = v_snapshotTasks_2370_;
v___y_2313_ = v_recordedDeps_2367_;
v___y_2314_ = v_auxDeclNGen_2365_;
v___y_2315_ = v___y_2357_;
v___y_2316_ = v___y_2358_;
v___y_2317_ = v___x_2372_;
goto v___jp_2306_;
}
else
{
lean_object* v_env_2373_; lean_object* v_nextMacroScope_2374_; lean_object* v_ngen_2375_; lean_object* v_auxDeclNGen_2376_; lean_object* v_traceState_2377_; lean_object* v_recordedDeps_2378_; lean_object* v_messages_2379_; lean_object* v_infoState_2380_; lean_object* v_snapshotTasks_2381_; lean_object* v_asyncMode_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_env_2373_ = lean_ctor_get(v___x_2359_, 0);
lean_inc_ref(v_env_2373_);
v_nextMacroScope_2374_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_nextMacroScope_2374_);
v_ngen_2375_ = lean_ctor_get(v___x_2359_, 2);
lean_inc_ref(v_ngen_2375_);
v_auxDeclNGen_2376_ = lean_ctor_get(v___x_2359_, 3);
lean_inc_ref(v_auxDeclNGen_2376_);
v_traceState_2377_ = lean_ctor_get(v___x_2359_, 4);
lean_inc_ref(v_traceState_2377_);
v_recordedDeps_2378_ = lean_ctor_get(v___x_2359_, 6);
lean_inc_ref(v_recordedDeps_2378_);
v_messages_2379_ = lean_ctor_get(v___x_2359_, 7);
lean_inc_ref(v_messages_2379_);
v_infoState_2380_ = lean_ctor_get(v___x_2359_, 8);
lean_inc_ref(v_infoState_2380_);
v_snapshotTasks_2381_ = lean_ctor_get(v___x_2359_, 9);
lean_inc_ref(v_snapshotTasks_2381_);
lean_dec(v___x_2359_);
v_asyncMode_2382_ = lean_ctor_get(v_toEnvExtension_2360_, 2);
lean_inc_ref_n(v_toEnvExtension_2360_, 2);
v___x_2383_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2360_, v_env_2373_);
lean_dec_ref(v_env_2373_);
v___x_2384_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2360_, v___x_2383_, v___f_2354_, v_asyncMode_2382_, v___x_2347_, v___x_2355_);
v___y_2307_ = v_traceState_2377_;
v___y_2308_ = v_infoState_2380_;
v___y_2309_ = v_messages_2379_;
v___y_2310_ = v_nextMacroScope_2374_;
v___y_2311_ = v_ngen_2375_;
v___y_2312_ = v_snapshotTasks_2381_;
v___y_2313_ = v_recordedDeps_2378_;
v___y_2314_ = v_auxDeclNGen_2376_;
v___y_2315_ = v___y_2357_;
v___y_2316_ = v___y_2358_;
v___y_2317_ = v___x_2384_;
goto v___jp_2306_;
}
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref_known(v_entry_2342_, 1);
lean_dec(v_hint_2298_);
lean_dec(v_mod_2296_);
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
v___jp_2306_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_mctx_2322_; lean_object* v_zetaDeltaFVarIds_2323_; lean_object* v_postponed_2324_; lean_object* v_diag_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2336_; 
v___x_2318_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_2319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2319_, 0, v___y_2317_);
lean_ctor_set(v___x_2319_, 1, v___y_2310_);
lean_ctor_set(v___x_2319_, 2, v___y_2311_);
lean_ctor_set(v___x_2319_, 3, v___y_2314_);
lean_ctor_set(v___x_2319_, 4, v___y_2307_);
lean_ctor_set(v___x_2319_, 5, v___x_2318_);
lean_ctor_set(v___x_2319_, 6, v___y_2313_);
lean_ctor_set(v___x_2319_, 7, v___y_2309_);
lean_ctor_set(v___x_2319_, 8, v___y_2308_);
lean_ctor_set(v___x_2319_, 9, v___y_2312_);
v___x_2320_ = lean_st_ref_put(v___y_2316_, v___x_2319_);
v___x_2321_ = lean_st_ref_take(v___y_2315_);
v_mctx_2322_ = lean_ctor_get(v___x_2321_, 0);
v_zetaDeltaFVarIds_2323_ = lean_ctor_get(v___x_2321_, 2);
v_postponed_2324_ = lean_ctor_get(v___x_2321_, 3);
v_diag_2325_ = lean_ctor_get(v___x_2321_, 4);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v___x_2321_, 1);
lean_dec(v_unused_2337_);
v___x_2327_ = v___x_2321_;
v_isShared_2328_ = v_isSharedCheck_2336_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_diag_2325_);
lean_inc(v_postponed_2324_);
lean_inc(v_zetaDeltaFVarIds_2323_);
lean_inc(v_mctx_2322_);
lean_dec(v___x_2321_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2336_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__5);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v___x_2330_);
v___x_2332_ = v___x_2327_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_mctx_2322_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_zetaDeltaFVarIds_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_postponed_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_diag_2325_);
v___x_2332_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_st_ref_put(v___y_2315_, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2329_);
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2420_, lean_object* v_isMeta_2421_, lean_object* v_hint_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v_isMeta_boxed_2430_; lean_object* v_res_2431_; 
v_isMeta_boxed_2430_ = lean_unbox(v_isMeta_2421_);
v_res_2431_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2420_, v_isMeta_boxed_2430_, v_hint_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2432_, lean_object* v_declName_2433_, lean_object* v_as_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec(v_declName_2433_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_b_2437_);
return v___x_2446_;
}
else
{
lean_object* v___x_2447_; lean_object* v_modules_2448_; lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2451_; lean_object* v_toImport_2452_; lean_object* v_module_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2447_ = l_Lean_Environment_header(v___x_2432_);
v_modules_2448_ = lean_ctor_get(v___x_2447_, 3);
lean_inc_ref(v_modules_2448_);
lean_dec_ref(v___x_2447_);
v___x_2449_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2450_ = lean_array_uget_borrowed(v_as_2434_, v_i_2436_);
v___x_2451_ = lean_array_get(v___x_2449_, v_modules_2448_, v_a_2450_);
lean_dec_ref(v_modules_2448_);
v_toImport_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc_ref(v_toImport_2452_);
lean_dec(v___x_2451_);
v_module_2453_ = lean_ctor_get(v_toImport_2452_, 0);
lean_inc(v_module_2453_);
lean_dec_ref(v_toImport_2452_);
v___x_2454_ = lean_box(0);
v___x_2455_ = 0;
lean_inc(v_declName_2433_);
v___x_2456_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2453_, v___x_2455_, v_declName_2433_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2456_) == 0)
{
size_t v___x_2457_; size_t v___x_2458_; 
lean_dec_ref_known(v___x_2456_, 1);
v___x_2457_ = ((size_t)1ULL);
v___x_2458_ = lean_usize_add(v_i_2436_, v___x_2457_);
v_i_2436_ = v___x_2458_;
v_b_2437_ = v___x_2454_;
goto _start;
}
else
{
lean_dec(v_declName_2433_);
return v___x_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2460_, lean_object* v_declName_2461_, lean_object* v_as_2462_, lean_object* v_sz_2463_, lean_object* v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2463_);
lean_dec(v_sz_2463_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2464_);
lean_dec(v_i_2464_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2460_, v_declName_2461_, v_as_2462_, v_sz_boxed_2473_, v_i_boxed_2474_, v_b_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v_as_2462_);
lean_dec_ref(v___x_2460_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(lean_object* v_a_2476_, lean_object* v_x_2477_){
_start:
{
if (lean_obj_tag(v_x_2477_) == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_box(0);
return v___x_2478_;
}
else
{
lean_object* v_key_2479_; lean_object* v_value_2480_; lean_object* v_tail_2481_; uint8_t v___x_2482_; 
v_key_2479_ = lean_ctor_get(v_x_2477_, 0);
v_value_2480_ = lean_ctor_get(v_x_2477_, 1);
v_tail_2481_ = lean_ctor_get(v_x_2477_, 2);
v___x_2482_ = lean_name_eq(v_key_2479_, v_a_2476_);
if (v___x_2482_ == 0)
{
v_x_2477_ = v_tail_2481_;
goto _start;
}
else
{
lean_object* v___x_2484_; 
lean_inc(v_value_2480_);
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_value_2480_);
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg___boxed(lean_object* v_a_2485_, lean_object* v_x_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(v_a_2485_, v_x_2486_);
lean_dec(v_x_2486_);
lean_dec(v_a_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_buckets_2490_; lean_object* v___x_2491_; uint64_t v___y_2493_; 
v_buckets_2490_ = lean_ctor_get(v_m_2488_, 1);
v___x_2491_ = lean_array_get_size(v_buckets_2490_);
if (lean_obj_tag(v_a_2489_) == 0)
{
uint64_t v___x_2507_; 
v___x_2507_ = 1723ULL;
v___y_2493_ = v___x_2507_;
goto v___jp_2492_;
}
else
{
uint64_t v_hash_2508_; 
v_hash_2508_ = lean_ctor_get_uint64(v_a_2489_, sizeof(void*)*2);
v___y_2493_ = v_hash_2508_;
goto v___jp_2492_;
}
v___jp_2492_:
{
uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v_fold_2496_; uint64_t v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2494_ = 32ULL;
v___x_2495_ = lean_uint64_shift_right(v___y_2493_, v___x_2494_);
v_fold_2496_ = lean_uint64_xor(v___y_2493_, v___x_2495_);
v___x_2497_ = 16ULL;
v___x_2498_ = lean_uint64_shift_right(v_fold_2496_, v___x_2497_);
v___x_2499_ = lean_uint64_xor(v_fold_2496_, v___x_2498_);
v___x_2500_ = lean_uint64_to_usize(v___x_2499_);
v___x_2501_ = lean_usize_of_nat(v___x_2491_);
v___x_2502_ = ((size_t)1ULL);
v___x_2503_ = lean_usize_sub(v___x_2501_, v___x_2502_);
v___x_2504_ = lean_usize_land(v___x_2500_, v___x_2503_);
v___x_2505_ = lean_array_uget_borrowed(v_buckets_2490_, v___x_2504_);
v___x_2506_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(v_a_2489_, v___x_2505_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_m_2509_);
return v_res_2511_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2515_, uint8_t v_isMeta_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v_env_2529_; lean_object* v___y_2531_; lean_object* v___x_2544_; 
v___x_2524_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0);
v___x_2525_ = lean_st_ref_get(v___y_2522_);
v_env_2529_ = lean_ctor_get(v___x_2525_, 0);
lean_inc_ref(v_env_2529_);
lean_dec(v___x_2525_);
v___x_2544_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2529_, v_declName_2515_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref(v_env_2529_);
lean_dec(v_declName_2515_);
goto v___jp_2526_;
}
else
{
lean_object* v_val_2545_; lean_object* v___x_2546_; lean_object* v_modules_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_val_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_val_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = l_Lean_Environment_header(v_env_2529_);
v_modules_2547_ = lean_ctor_get(v___x_2546_, 3);
lean_inc_ref(v_modules_2547_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = lean_array_get_size(v_modules_2547_);
v___x_2549_ = lean_nat_dec_lt(v_val_2545_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_dec_ref(v_modules_2547_);
lean_dec(v_val_2545_);
lean_dec_ref(v_env_2529_);
lean_dec(v_declName_2515_);
goto v___jp_2526_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___y_2553_; 
v___x_2550_ = lean_array_fget(v_modules_2547_, v_val_2545_);
lean_dec(v_val_2545_);
lean_dec_ref(v_modules_2547_);
v___x_2551_ = lean_st_ref_get(v___y_2522_);
if (v_isMeta_2516_ == 0)
{
lean_dec(v___x_2551_);
v___y_2553_ = v_isMeta_2516_;
goto v___jp_2552_;
}
else
{
lean_object* v_env_2564_; uint8_t v___x_2565_; 
v_env_2564_ = lean_ctor_get(v___x_2551_, 0);
lean_inc_ref(v_env_2564_);
lean_dec(v___x_2551_);
lean_inc(v_declName_2515_);
v___x_2565_ = l_Lean_isMarkedMeta(v_env_2564_, v_declName_2515_);
if (v___x_2565_ == 0)
{
v___y_2553_ = v_isMeta_2516_;
goto v___jp_2552_;
}
else
{
uint8_t v___x_2566_; 
v___x_2566_ = 0;
v___y_2553_ = v___x_2566_;
goto v___jp_2552_;
}
}
v___jp_2552_:
{
lean_object* v_toImport_2554_; lean_object* v_module_2555_; lean_object* v___x_2556_; 
v_toImport_2554_ = lean_ctor_get(v___x_2550_, 0);
lean_inc_ref(v_toImport_2554_);
lean_dec(v___x_2550_);
v_module_2555_ = lean_ctor_get(v_toImport_2554_, 0);
lean_inc(v_module_2555_);
lean_dec_ref(v_toImport_2554_);
lean_inc(v_declName_2515_);
v___x_2556_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2555_, v___y_2553_, v_declName_2515_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec_ref_known(v___x_2556_, 1);
v___x_2557_ = l_Lean_indirectModUseExt;
v___x_2558_ = lean_box(1);
v___x_2559_ = lean_box(0);
lean_inc_ref(v_env_2529_);
v___x_2560_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2524_, v___x_2557_, v_env_2529_, v___x_2558_, v___x_2559_);
v___x_2561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2560_, v_declName_2515_);
lean_dec(v___x_2560_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___y_2531_ = v___x_2562_;
goto v___jp_2530_;
}
else
{
lean_object* v_val_2563_; 
v_val_2563_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v___x_2561_, 1);
v___y_2531_ = v_val_2563_;
goto v___jp_2530_;
}
}
else
{
lean_dec_ref(v_env_2529_);
lean_dec(v_declName_2515_);
return v___x_2556_;
}
}
}
}
v___jp_2526_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
v___jp_2530_:
{
lean_object* v___x_2532_; size_t v_sz_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2532_ = lean_box(0);
v_sz_2533_ = lean_array_size(v___y_2531_);
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2529_, v_declName_2515_, v___y_2531_, v_sz_2533_, v___x_2534_, v___x_2532_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_env_2529_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2535_, 0);
lean_dec(v_unused_2543_);
v___x_2537_ = v___x_2535_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_dec(v___x_2535_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2532_);
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2532_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
return v___x_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2567_, lean_object* v_isMeta_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v_isMeta_boxed_2576_; lean_object* v_res_2577_; 
v_isMeta_boxed_2576_ = lean_unbox(v_isMeta_2568_);
v_res_2577_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2567_, v_isMeta_boxed_2576_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2578_, lean_object* v_b_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
if (lean_obj_tag(v_as_x27_2578_) == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_b_2579_);
return v___x_2587_;
}
else
{
lean_object* v_head_2588_; lean_object* v_tail_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
v_head_2588_ = lean_ctor_get(v_as_x27_2578_, 0);
v_tail_2589_ = lean_ctor_get(v_as_x27_2578_, 1);
v___x_2590_ = lean_box(0);
v___x_2591_ = 1;
lean_inc(v_head_2588_);
v___x_2592_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2588_, v___x_2591_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref_known(v___x_2592_, 1);
v_as_x27_2578_ = v_tail_2589_;
v_b_2579_ = v___x_2590_;
goto _start;
}
else
{
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2594_, lean_object* v_b_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2594_, v_b_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_as_x27_2594_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_env_2604_, lean_object* v___x_2605_, lean_object* v_currNamespace_2606_, lean_object* v_openDecls_2607_, lean_object* v_n_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = l_Lean_ResolveName_resolveGlobalName(v_env_2604_, v___x_2605_, v_currNamespace_2606_, v_openDecls_2607_, v_n_2608_);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___y_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_env_2613_, lean_object* v___x_2614_, lean_object* v_currNamespace_2615_, lean_object* v_openDecls_2616_, lean_object* v_n_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_env_2613_, v___x_2614_, v_currNamespace_2615_, v_openDecls_2616_, v_n_2617_, v___y_2618_, v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___x_2614_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2621_, lean_object* v_declName_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v___x_2625_; lean_object* v_env_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; uint8_t v___x_2629_; 
v___x_2625_ = 0;
v_env_2626_ = l_Lean_Environment_setExporting(v_env_2621_, v___x_2625_);
lean_inc(v_declName_2622_);
v___x_2627_ = l_Lean_mkPrivateName(v_env_2626_, v_declName_2622_);
v___x_2628_ = 1;
lean_inc_ref(v_env_2626_);
v___x_2629_ = l_Lean_Environment_contains(v_env_2626_, v___x_2627_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = l_Lean_privateToUserName(v_declName_2622_);
v___x_2631_ = l_Lean_Environment_contains(v_env_2626_, v___x_2630_, v___x_2628_);
v___x_2632_ = lean_box(v___x_2631_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___y_2624_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v_env_2626_);
lean_dec(v_declName_2622_);
v___x_2634_ = lean_box(v___x_2629_);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___y_2624_);
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2636_, lean_object* v_declName_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2636_, v_declName_2637_, v___y_2638_, v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2640_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = l_Lean_maxRecDepthErrorMessage;
v___x_2647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2649_ = l_Lean_MessageData_ofFormat(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2651_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2652_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v___x_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_ref_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v_toCold_2671_; lean_object* v_env_2672_; lean_object* v_currRecDepth_2673_; lean_object* v_ref_2674_; lean_object* v_maxRecDepth_2675_; lean_object* v_currNamespace_2676_; lean_object* v_openDecls_2677_; lean_object* v_quotContext_2678_; lean_object* v_currMacroScope_2679_; lean_object* v___f_2680_; lean_object* v___f_2681_; lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v_methods_2686_; lean_object* v___x_2687_; lean_object* v_nextMacroScope_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2670_ = lean_st_ref_get(v___y_2668_);
v_toCold_2671_ = lean_ctor_get(v___y_2667_, 0);
v_env_2672_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_ref_n(v_env_2672_, 4);
lean_dec(v___x_2670_);
v_currRecDepth_2673_ = lean_ctor_get(v___y_2667_, 1);
v_ref_2674_ = lean_ctor_get(v___y_2667_, 2);
v_maxRecDepth_2675_ = lean_ctor_get(v_toCold_2671_, 3);
v_currNamespace_2676_ = lean_ctor_get(v_toCold_2671_, 4);
v_openDecls_2677_ = lean_ctor_get(v_toCold_2671_, 5);
v_quotContext_2678_ = lean_ctor_get(v_toCold_2671_, 8);
v_currMacroScope_2679_ = lean_ctor_get(v_toCold_2671_, 9);
v___f_2680_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2680_, 0, v_env_2672_);
v___f_2681_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2681_, 0, v_env_2672_);
v___x_2682_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2667_);
lean_inc_n(v_currNamespace_2676_, 3);
v___f_2683_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2683_, 0, v_currNamespace_2676_);
lean_inc_n(v_openDecls_2677_, 2);
v___f_2684_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2684_, 0, v_env_2672_);
lean_closure_set(v___f_2684_, 1, v___x_2682_);
lean_closure_set(v___f_2684_, 2, v_currNamespace_2676_);
lean_closure_set(v___f_2684_, 3, v_openDecls_2677_);
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2685_, 0, v_env_2672_);
lean_closure_set(v___f_2685_, 1, v_currNamespace_2676_);
lean_closure_set(v___f_2685_, 2, v_openDecls_2677_);
v_methods_2686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2686_, 0, v___f_2681_);
lean_ctor_set(v_methods_2686_, 1, v___f_2683_);
lean_ctor_set(v_methods_2686_, 2, v___f_2680_);
lean_ctor_set(v_methods_2686_, 3, v___f_2685_);
lean_ctor_set(v_methods_2686_, 4, v___f_2684_);
v___x_2687_ = lean_st_ref_get(v___y_2668_);
v_nextMacroScope_2688_ = lean_ctor_get(v___x_2687_, 1);
lean_inc(v_nextMacroScope_2688_);
lean_dec(v___x_2687_);
lean_inc(v_ref_2674_);
lean_inc(v_maxRecDepth_2675_);
lean_inc(v_currRecDepth_2673_);
lean_inc(v_currMacroScope_2679_);
lean_inc(v_quotContext_2678_);
v___x_2689_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2689_, 0, v_methods_2686_);
lean_ctor_set(v___x_2689_, 1, v_quotContext_2678_);
lean_ctor_set(v___x_2689_, 2, v_currMacroScope_2679_);
lean_ctor_set(v___x_2689_, 3, v_currRecDepth_2673_);
lean_ctor_set(v___x_2689_, 4, v_maxRecDepth_2675_);
lean_ctor_set(v___x_2689_, 5, v_ref_2674_);
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2691_, 0, v_nextMacroScope_2688_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
lean_ctor_set(v___x_2691_, 2, v___x_2690_);
v___x_2692_ = lean_apply_2(v_x_2662_, v___x_2689_, v___x_2691_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v_a_2694_; lean_object* v_macroScope_2695_; lean_object* v_traceMsgs_2696_; lean_object* v_expandedMacroDecls_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_a_2693_);
v_a_2694_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2692_, 2);
v_macroScope_2695_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_macroScope_2695_);
v_traceMsgs_2696_ = lean_ctor_get(v_a_2693_, 1);
lean_inc(v_traceMsgs_2696_);
v_expandedMacroDecls_2697_ = lean_ctor_get(v_a_2693_, 2);
lean_inc(v_expandedMacroDecls_2697_);
lean_dec(v_a_2693_);
v___x_2698_ = lean_box(0);
v___x_2699_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2697_, v___x_2698_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v_expandedMacroDecls_2697_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2700_; lean_object* v_env_2701_; lean_object* v_ngen_2702_; lean_object* v_auxDeclNGen_2703_; lean_object* v_traceState_2704_; lean_object* v_cache_2705_; lean_object* v_recordedDeps_2706_; lean_object* v_messages_2707_; lean_object* v_infoState_2708_; lean_object* v_snapshotTasks_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref_known(v___x_2699_, 1);
v___x_2700_ = lean_st_ref_take(v___y_2668_);
v_env_2701_ = lean_ctor_get(v___x_2700_, 0);
v_ngen_2702_ = lean_ctor_get(v___x_2700_, 2);
v_auxDeclNGen_2703_ = lean_ctor_get(v___x_2700_, 3);
v_traceState_2704_ = lean_ctor_get(v___x_2700_, 4);
v_cache_2705_ = lean_ctor_get(v___x_2700_, 5);
v_recordedDeps_2706_ = lean_ctor_get(v___x_2700_, 6);
v_messages_2707_ = lean_ctor_get(v___x_2700_, 7);
v_infoState_2708_ = lean_ctor_get(v___x_2700_, 8);
v_snapshotTasks_2709_ = lean_ctor_get(v___x_2700_, 9);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2700_, 1);
lean_dec(v_unused_2736_);
v___x_2711_ = v___x_2700_;
v_isShared_2712_ = v_isSharedCheck_2735_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snapshotTasks_2709_);
lean_inc(v_infoState_2708_);
lean_inc(v_messages_2707_);
lean_inc(v_recordedDeps_2706_);
lean_inc(v_cache_2705_);
lean_inc(v_traceState_2704_);
lean_inc(v_auxDeclNGen_2703_);
lean_inc(v_ngen_2702_);
lean_inc(v_env_2701_);
lean_dec(v___x_2700_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2735_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_macroScope_2695_);
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_env_2701_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_macroScope_2695_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_ngen_2702_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v_auxDeclNGen_2703_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_traceState_2704_);
lean_ctor_set(v_reuseFailAlloc_2734_, 5, v_cache_2705_);
lean_ctor_set(v_reuseFailAlloc_2734_, 6, v_recordedDeps_2706_);
lean_ctor_set(v_reuseFailAlloc_2734_, 7, v_messages_2707_);
lean_ctor_set(v_reuseFailAlloc_2734_, 8, v_infoState_2708_);
lean_ctor_set(v_reuseFailAlloc_2734_, 9, v_snapshotTasks_2709_);
v___x_2714_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_st_ref_put(v___y_2668_, v___x_2714_);
v___x_2716_ = l_List_reverse___redArg(v_traceMsgs_2696_);
v___x_2717_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2716_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; 
v_unused_2725_ = lean_ctor_get(v___x_2717_, 0);
lean_dec(v_unused_2725_);
v___x_2719_ = v___x_2717_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_dec(v___x_2717_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_a_2694_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2694_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2694_);
v_a_2726_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2717_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2717_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_traceMsgs_2696_);
lean_dec(v_macroScope_2695_);
lean_dec(v_a_2694_);
v_a_2737_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2699_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2699_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v_a_2745_; 
v_a_2745_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2692_, 2);
if (lean_obj_tag(v_a_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v_a_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v_a_2746_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_a_2746_);
v_a_2747_ = lean_ctor_get(v_a_2745_, 1);
lean_inc_ref(v_a_2747_);
lean_dec_ref_known(v_a_2745_, 2);
v___x_2748_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2749_ = lean_string_dec_eq(v_a_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_a_2747_);
v___x_2751_ = l_Lean_MessageData_ofFormat(v___x_2750_);
v___x_2752_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2746_, v___x_2751_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v_a_2746_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; 
lean_dec_ref(v_a_2747_);
v___x_2753_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2746_);
return v___x_2753_;
}
}
else
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2763_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2769_ = l_Lean_mkConst(v___x_2768_, v___x_2767_);
return v___x_2769_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2780_ = l_Lean_mkConst(v___x_2779_, v___x_2778_);
return v___x_2780_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2783_, lean_object* v_as_2784_, size_t v_sz_2785_, size_t v_i_2786_, lean_object* v_b_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_a_2796_; uint8_t v___x_2800_; 
v___x_2800_ = lean_usize_dec_lt(v_i_2786_, v_sz_2785_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_b_2787_);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v_a_2804_; uint8_t v___x_2805_; 
v___x_2802_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2803_ = lean_box(0);
v_a_2804_ = lean_array_uget_borrowed(v_as_2784_, v_i_2786_);
lean_inc(v_a_2804_);
v___x_2805_ = l_Lean_Syntax_isOfKind(v_a_2804_, v___x_2802_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref_known(v___x_2806_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2806_;
}
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_unsigned_to_nat(1u);
v___x_2809_ = l_Lean_Syntax_getArg(v_a_2804_, v___x_2807_);
v___x_2810_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2809_);
v___x_2811_ = l_Lean_Syntax_isOfKind(v___x_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2809_);
v___x_2813_ = l_Lean_Syntax_isOfKind(v___x_2809_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec(v___x_2809_);
v___x_2814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref_known(v___x_2814_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2814_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = l_Lean_Syntax_getArg(v___x_2809_, v___x_2807_);
v___x_2816_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2815_);
v___x_2817_ = l_Lean_Syntax_isOfKind(v___x_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec(v___x_2815_);
lean_dec(v___x_2809_);
v___x_2818_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_dec_ref_known(v___x_2818_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2818_;
}
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2819_ = l_Lean_Syntax_getArg(v___x_2809_, v___x_2808_);
lean_dec(v___x_2809_);
v___x_2820_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2819_);
v___x_2821_ = l_Lean_Syntax_isOfKind(v___x_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; 
lean_dec(v___x_2819_);
lean_dec(v___x_2815_);
v___x_2822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_dec_ref_known(v___x_2822_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2822_;
}
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2824_, 0, v___x_2815_);
v___x_2825_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2824_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l_Lean_Widget_elabWidgetInstanceSpec(v___x_2819_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc_n(v_a_2828_, 2);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2828_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2829_) == 0)
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_unbox(v_a_2826_);
if (v___x_2830_ == 1)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2826_);
v_a_2831_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2832_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2831_, v___y_2791_, v___y_2793_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_dec_ref_known(v___x_2832_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2832_;
}
}
else
{
lean_object* v_a_2833_; lean_object* v_id_2834_; uint64_t v_javascriptHash_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_a_2833_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2829_, 1);
v_id_2834_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_id_2834_);
v_javascriptHash_2835_ = lean_ctor_get_uint64(v_a_2833_, sizeof(void*)*2);
lean_dec(v_a_2833_);
v___x_2836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1));
v___x_2837_ = l_Lean_Name_append(v_id_2834_, v___x_2836_);
v___x_2838_ = l_Lean_Core_mkFreshUserName(v___x_2837_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2828_, v___y_2791_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; uint8_t v___x_2860_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2840_, 1);
v___x_2860_ = l_Lean_Expr_hasMVar(v_a_2841_);
if (v___x_2860_ == 0)
{
v___y_2843_ = v___y_2788_;
v___y_2844_ = v___y_2789_;
v___y_2845_ = v___y_2790_;
v___y_2846_ = v___y_2791_;
v___y_2847_ = v___y_2792_;
v___y_2848_ = v___y_2793_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2841_);
v___x_2862_ = l_Lean_indentExpr(v_a_2841_);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2863_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref_known(v___x_2864_, 1);
v___y_2843_ = v___y_2788_;
v___y_2844_ = v___y_2789_;
v___y_2845_ = v___y_2790_;
v___y_2846_ = v___y_2791_;
v___y_2847_ = v___y_2792_;
v___y_2848_ = v___y_2793_;
goto v___jp_2842_;
}
else
{
lean_dec(v_a_2841_);
lean_dec(v_a_2839_);
lean_dec(v_a_2826_);
return v___x_2864_;
}
}
v___jp_2842_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2849_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
lean_inc_n(v_a_2839_, 2);
v___x_2850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2839_);
lean_ctor_set(v___x_2850_, 1, v___x_2823_);
lean_ctor_set(v___x_2850_, 2, v___x_2849_);
v___x_2851_ = lean_box(0);
v___x_2852_ = 1;
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2839_);
lean_ctor_set(v___x_2853_, 1, v___x_2823_);
v___x_2854_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2854_, 0, v___x_2850_);
lean_ctor_set(v___x_2854_, 1, v_a_2841_);
lean_ctor_set(v___x_2854_, 2, v___x_2851_);
lean_ctor_set(v___x_2854_, 3, v___x_2853_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*4, v___x_2852_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
v___x_2856_ = l_Lean_addAndCompile(v___x_2855_, v___x_2783_, v___x_2811_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2856_) == 0)
{
uint8_t v___x_2857_; 
lean_dec_ref_known(v___x_2856_, 1);
v___x_2857_ = lean_unbox(v_a_2826_);
lean_dec(v_a_2826_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_2835_, v_a_2839_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_dec_ref_known(v___x_2858_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2858_;
}
}
else
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_2835_, v_a_2839_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_dec_ref_known(v___x_2859_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2859_;
}
}
}
else
{
lean_dec(v_a_2839_);
lean_dec(v_a_2826_);
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2839_);
lean_dec(v_a_2826_);
v_a_2865_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2840_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2840_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2826_);
v_a_2873_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2838_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2838_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2826_);
v_a_2881_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2829_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2829_);
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
lean_dec(v_a_2826_);
v_a_2889_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2827_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2827_);
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
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v___x_2819_);
v_a_2897_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2825_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2825_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = l_Lean_Syntax_getArg(v___x_2809_, v___x_2808_);
lean_dec(v___x_2809_);
v___x_2906_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2905_);
v___x_2907_ = l_Lean_Syntax_isOfKind(v___x_2905_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_dec(v___x_2905_);
v___x_2908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_dec_ref_known(v___x_2908_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2908_;
}
}
else
{
lean_object* v_toCold_2909_; lean_object* v_ref_2910_; lean_object* v_quotContext_2911_; lean_object* v_currMacroScope_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_toCold_2909_ = lean_ctor_get(v___y_2792_, 0);
v_ref_2910_ = lean_ctor_get(v___y_2792_, 2);
v_quotContext_2911_ = lean_ctor_get(v_toCold_2909_, 8);
v_currMacroScope_2912_ = lean_ctor_get(v_toCold_2909_, 9);
v___x_2913_ = 0;
v___x_2914_ = l_Lean_SourceInfo_fromRef(v_ref_2910_, v___x_2913_);
v___x_2915_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2916_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2917_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2912_);
lean_inc(v_quotContext_2911_);
v___x_2918_ = l_Lean_addMacroScope(v_quotContext_2911_, v___x_2917_, v_currMacroScope_2912_);
v___x_2919_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2914_, 2);
v___x_2920_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2914_);
lean_ctor_set(v___x_2920_, 1, v___x_2916_);
lean_ctor_set(v___x_2920_, 2, v___x_2918_);
lean_ctor_set(v___x_2920_, 3, v___x_2919_);
v___x_2921_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2922_ = l_Lean_Syntax_node1(v___x_2914_, v___x_2921_, v___x_2905_);
v___x_2923_ = l_Lean_Syntax_node2(v___x_2914_, v___x_2915_, v___x_2920_, v___x_2922_);
v___x_2924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2925_ = l_Lean_Elab_Term_elabTerm(v___x_2923_, v___x_2924_, v___x_2783_, v___x_2783_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2926_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; uint64_t v_javascriptHash_2929_; lean_object* v___x_2930_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v_javascriptHash_2929_ = lean_ctor_get_uint64(v_a_2928_, sizeof(void*)*1);
lean_dec(v_a_2928_);
v___x_2930_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2929_, v___y_2791_, v___y_2793_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_dec_ref_known(v___x_2930_, 1);
v_a_2796_ = v___x_2803_;
goto v___jp_2795_;
}
else
{
return v___x_2930_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_a_2931_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2927_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2927_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2925_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2925_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
}
}
v___jp_2795_:
{
size_t v___x_2797_; size_t v___x_2798_; 
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2786_, v___x_2797_);
v_i_2786_ = v___x_2798_;
v_b_2787_ = v_a_2796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2947_, lean_object* v_as_2948_, lean_object* v_sz_2949_, lean_object* v_i_2950_, lean_object* v_b_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
uint8_t v___x_31208__boxed_2959_; size_t v_sz_boxed_2960_; size_t v_i_boxed_2961_; lean_object* v_res_2962_; 
v___x_31208__boxed_2959_ = lean_unbox(v___x_2947_);
v_sz_boxed_2960_ = lean_unbox_usize(v_sz_2949_);
lean_dec(v_sz_2949_);
v_i_boxed_2961_ = lean_unbox_usize(v_i_2950_);
lean_dec(v_i_2950_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_31208__boxed_2959_, v_as_2948_, v_sz_boxed_2960_, v_i_boxed_2961_, v_b_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v_as_2948_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2963_, lean_object* v___x_2964_, size_t v_sz_2965_, size_t v___x_2966_, lean_object* v___x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2963_, v___x_2964_, v_sz_2965_, v___x_2966_, v___x_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_2983_);
v___x_2977_ = v___x_2975_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_dec(v___x_2975_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2967_);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2967_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_2984_, lean_object* v___x_2985_, lean_object* v_sz_2986_, lean_object* v___x_2987_, lean_object* v___x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
uint8_t v___x_31560__boxed_2996_; size_t v_sz_boxed_2997_; size_t v___x_31562__boxed_2998_; lean_object* v_res_2999_; 
v___x_31560__boxed_2996_ = lean_unbox(v___x_2984_);
v_sz_boxed_2997_ = lean_unbox_usize(v_sz_2986_);
lean_dec(v_sz_2986_);
v___x_31562__boxed_2998_ = lean_unbox_usize(v___x_2987_);
lean_dec(v___x_2987_);
v_res_2999_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_31560__boxed_2996_, v___x_2985_, v_sz_boxed_2997_, v___x_31562__boxed_2998_, v___x_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v___x_2985_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_3002_);
v___x_3007_ = l_Lean_Syntax_isOfKind(v_x_3002_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec(v_x_3002_);
v___x_3008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_ws_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; size_t v_sz_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; 
v___x_3009_ = lean_unsigned_to_nat(2u);
v___x_3010_ = l_Lean_Syntax_getArg(v_x_3002_, v___x_3009_);
lean_dec(v_x_3002_);
v_ws_3011_ = l_Lean_Syntax_getArgs(v___x_3010_);
lean_dec(v___x_3010_);
v___x_3012_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_3011_);
lean_dec_ref(v_ws_3011_);
v___x_3013_ = lean_box(0);
v_sz_3014_ = lean_array_size(v___x_3012_);
v___x_3015_ = lean_box(v___x_3007_);
v___x_3016_ = lean_box_usize(v_sz_3014_);
v___x_3017_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3018_, 0, v___x_3015_);
lean_closure_set(v___f_3018_, 1, v___x_3012_);
lean_closure_set(v___f_3018_, 2, v___x_3016_);
lean_closure_set(v___f_3018_, 3, v___x_3017_);
lean_closure_set(v___f_3018_, 4, v___x_3013_);
v___x_3019_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3018_, v_a_3003_, v_a_3004_);
return v___x_3019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_3025_, lean_object* v_x_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_3026_, v___y_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3030_, lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_3030_, v_x_3031_, v___y_3032_, v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v_x_3031_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_3035_, lean_object* v_ref_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_3036_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3045_, lean_object* v_ref_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3045_, v_ref_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3065_, lean_object* v_x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3065_, v_x_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3075_, v___y_3079_, v___y_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3093_, lean_object* v_msg_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3103_, v_msg_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3113_, v___y_3117_, v___y_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
uint64_t v_h_boxed_3130_; lean_object* v_res_3131_; 
v_h_boxed_3130_ = lean_unbox_uint64(v_h_3122_);
lean_dec_ref(v_h_3122_);
v_res_3131_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3130_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3132_, lean_object* v_msg_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3132_, v_msg_3133_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3142_, lean_object* v_msg_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3142_, v_msg_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3152_, lean_object* v_as_x27_3153_, lean_object* v_b_3154_, lean_object* v_a_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3153_, v_b_3154_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3164_, lean_object* v_as_x27_3165_, lean_object* v_b_3166_, lean_object* v_a_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3164_, v_as_x27_3165_, v_b_3166_, v_a_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v_as_x27_3165_);
lean_dec(v_as_3164_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3176_, lean_object* v_ref_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3177_, v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3187_, lean_object* v_ref_3188_, lean_object* v_msg_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3187_, v_ref_3188_, v_msg_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v_ref_3188_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3198_, lean_object* v_t_3199_, uint64_t v_k_3200_, lean_object* v_fallback_3201_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3199_, v_k_3200_, v_fallback_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3203_, lean_object* v_t_3204_, lean_object* v_k_3205_, lean_object* v_fallback_3206_){
_start:
{
uint64_t v_k_boxed_3207_; lean_object* v_res_3208_; 
v_k_boxed_3207_ = lean_unbox_uint64(v_k_3205_);
lean_dec_ref(v_k_3205_);
v_res_3208_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3203_, v_t_3204_, v_k_boxed_3207_, v_fallback_3206_);
lean_dec(v_fallback_3206_);
lean_dec(v_t_3204_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3209_, uint64_t v_k_3210_, lean_object* v_v_3211_, lean_object* v_t_3212_, lean_object* v_hl_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3210_, v_v_3211_, v_t_3212_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3215_, lean_object* v_k_3216_, lean_object* v_v_3217_, lean_object* v_t_3218_, lean_object* v_hl_3219_){
_start:
{
uint64_t v_k_boxed_3220_; lean_object* v_res_3221_; 
v_k_boxed_3220_ = lean_unbox_uint64(v_k_3216_);
lean_dec_ref(v_k_3216_);
v_res_3221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3215_, v_k_boxed_3220_, v_v_3217_, v_t_3218_, v_hl_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16(lean_object* v_00_u03b2_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg___boxed(lean_object* v___dummy_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg();
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11(lean_object* v_00_u03b2_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(lean_object* v_00_u03b1_3230_, lean_object* v_00_u03b2_3231_, lean_object* v_00_u03c3_3232_, lean_object* v_ext_3233_, lean_object* v_b_3234_, uint8_t v_kind_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v_ext_3233_, v_b_3234_, v_kind_3235_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___boxed(lean_object* v_00_u03b1_3244_, lean_object* v_00_u03b2_3245_, lean_object* v_00_u03c3_3246_, lean_object* v_ext_3247_, lean_object* v_b_3248_, lean_object* v_kind_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_kind_boxed_3257_; lean_object* v_res_3258_; 
v_kind_boxed_3257_ = lean_unbox(v_kind_3249_);
v_res_3258_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(v_00_u03b1_3244_, v_00_u03b2_3245_, v_00_u03c3_3246_, v_ext_3247_, v_b_3248_, v_kind_boxed_3257_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(lean_object* v_msgData_3259_, lean_object* v_macroStack_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_msgData_3259_, v_macroStack_3260_, v___y_3265_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___boxed(lean_object* v_msgData_3269_, lean_object* v_macroStack_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(v_msgData_3269_, v_macroStack_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(lean_object* v_00_u03b2_3279_, uint64_t v_k_3280_, lean_object* v_t_3281_, lean_object* v_h_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_3280_, v_t_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___boxed(lean_object* v_00_u03b2_3284_, lean_object* v_k_3285_, lean_object* v_t_3286_, lean_object* v_h_3287_){
_start:
{
uint64_t v_k_boxed_3288_; lean_object* v_res_3289_; 
v_k_boxed_3288_ = lean_unbox_uint64(v_k_3285_);
lean_dec_ref(v_k_3285_);
v_res_3289_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(v_00_u03b2_3284_, v_k_boxed_3288_, v_t_3286_, v_h_3287_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3290_, lean_object* v_m_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3291_, v_a_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3294_, lean_object* v_m_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3294_, v_m_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_m_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14(lean_object* v_00_u03b2_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
uint8_t v___x_3301_; 
v___x_3301_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(v_x_3299_, v_x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___boxed(lean_object* v_00_u03b2_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
uint8_t v_res_3305_; lean_object* v_r_3306_; 
v_res_3305_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14(v_00_u03b2_3302_, v_x_3303_, v_x_3304_);
lean_dec_ref(v_x_3304_);
lean_dec_ref(v_x_3303_);
v_r_3306_ = lean_box(v_res_3305_);
return v_r_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17(lean_object* v_00_u03b2_3307_, lean_object* v_a_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(v_a_3308_, v_x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___boxed(lean_object* v_00_u03b2_3311_, lean_object* v_a_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17(v_00_u03b2_3311_, v_a_3312_, v_x_3313_);
lean_dec(v_x_3313_);
lean_dec(v_a_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26(lean_object* v_00_u03b2_3315_, lean_object* v_x_3316_, size_t v_x_3317_, lean_object* v_x_3318_){
_start:
{
uint8_t v___x_3319_; 
v___x_3319_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(v_x_3316_, v_x_3317_, v_x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___boxed(lean_object* v_00_u03b2_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
size_t v_x_31933__boxed_3324_; uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_x_31933__boxed_3324_ = lean_unbox_usize(v_x_3322_);
lean_dec(v_x_3322_);
v_res_3325_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26(v_00_u03b2_3320_, v_x_3321_, v_x_31933__boxed_3324_, v_x_3323_);
lean_dec_ref(v_x_3323_);
lean_dec_ref(v_x_3321_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30(lean_object* v_00_u03b2_3327_, lean_object* v_keys_3328_, lean_object* v_vals_3329_, lean_object* v_heq_3330_, lean_object* v_i_3331_, lean_object* v_k_3332_){
_start:
{
uint8_t v___x_3333_; 
v___x_3333_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(v_keys_3328_, v_i_3331_, v_k_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___boxed(lean_object* v_00_u03b2_3334_, lean_object* v_keys_3335_, lean_object* v_vals_3336_, lean_object* v_heq_3337_, lean_object* v_i_3338_, lean_object* v_k_3339_){
_start:
{
uint8_t v_res_3340_; lean_object* v_r_3341_; 
v_res_3340_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30(v_00_u03b2_3334_, v_keys_3335_, v_vals_3336_, v_heq_3337_, v_i_3338_, v_k_3339_);
lean_dec_ref(v_k_3339_);
lean_dec_ref(v_vals_3336_);
lean_dec_ref(v_keys_3335_);
v_r_3341_ = lean_box(v_res_3340_);
return v_r_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3359_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3370_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
v___x_3370_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3369_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; uint64_t v_javascriptHash_3372_; lean_object* v_props_3373_; lean_object* v___x_3374_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v_javascriptHash_3372_ = lean_ctor_get_uint64(v_a_3371_, sizeof(void*)*2);
v_props_3373_ = lean_ctor_get(v_a_3371_, 1);
lean_inc_ref(v_props_3373_);
lean_dec(v_a_3371_);
v___x_3374_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3372_, v_props_3373_, v_x_3360_, v___y_3365_, v___y_3366_);
return v___x_3374_;
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_x_3360_);
v_a_3375_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3370_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3370_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec(v_x_3360_);
v_a_3383_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3368_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3368_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3391_, lean_object* v_x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3391_, v_x_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3401_);
v___x_3406_ = l_Lean_Syntax_isOfKind(v_x_3401_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
lean_dec(v_x_3401_);
v___x_3407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3407_;
}
else
{
lean_object* v___x_3408_; lean_object* v_s_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; 
v___x_3408_ = lean_unsigned_to_nat(1u);
v_s_3409_ = l_Lean_Syntax_getArg(v_x_3401_, v___x_3408_);
v___f_3410_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3410_, 0, v_s_3409_);
lean_closure_set(v___f_3410_, 1, v_x_3401_);
v___x_3411_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3410_, v_a_3402_, v_a_3403_);
return v___x_3411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Widget_elabWidgetCmd(v_x_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
return v_res_3416_;
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
