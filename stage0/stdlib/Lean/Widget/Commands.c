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
v___x_844_ = lean_nat_add(v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec(v___y_842_);
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
lean_ctor_set(v___x_824_, 3, v___y_841_);
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
lean_ctor_set(v_reuseFailAlloc_849_, 3, v___y_841_);
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
v___y_841_ = v___x_855_;
v___y_842_ = v___x_856_;
v___y_843_ = v_size_857_;
goto v___jp_840_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___y_841_ = v___x_855_;
v___y_842_ = v___x_856_;
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
v___x_985_ = lean_nat_add(v___y_982_, v___y_984_);
lean_dec(v___y_984_);
lean_dec(v___y_982_);
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
lean_ctor_set(v___x_989_, 3, v___y_983_);
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
lean_ctor_set(v_reuseFailAlloc_993_, 3, v___y_983_);
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
v___y_982_ = v___x_1007_;
v___y_983_ = v___x_1006_;
v___y_984_ = v_size_1008_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___y_982_ = v___x_1007_;
v___y_983_ = v___x_1006_;
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
v___x_1143_ = lean_nat_add(v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v___y_1141_);
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
lean_ctor_set(v___x_1123_, 3, v___y_1140_);
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
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v___y_1140_);
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
v___y_1140_ = v___x_1154_;
v___y_1141_ = v___x_1155_;
v___y_1142_ = v_size_1156_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___y_1140_ = v___x_1154_;
v___y_1141_ = v___x_1155_;
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
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1299_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
v___x_1300_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v___x_1298_);
lean_ctor_set(v___x_1300_, 3, v___x_1298_);
lean_ctor_set(v___x_1300_, 4, v___x_1298_);
lean_ctor_set(v___x_1300_, 5, v___x_1298_);
lean_ctor_set(v___x_1300_, 6, v___x_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v_env_1308_; lean_object* v_nextMacroScope_1309_; lean_object* v_ngen_1310_; lean_object* v_auxDeclNGen_1311_; lean_object* v_traceState_1312_; lean_object* v_recordedDeps_1313_; lean_object* v_messages_1314_; lean_object* v_infoState_1315_; lean_object* v_snapshotTasks_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1344_; 
v___x_1305_ = lean_box_uint64(v_h_1301_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1306_, 0, v___x_1305_);
v___x_1307_ = lean_st_ref_take(v___y_1303_);
v_env_1308_ = lean_ctor_get(v___x_1307_, 0);
v_nextMacroScope_1309_ = lean_ctor_get(v___x_1307_, 1);
v_ngen_1310_ = lean_ctor_get(v___x_1307_, 2);
v_auxDeclNGen_1311_ = lean_ctor_get(v___x_1307_, 3);
v_traceState_1312_ = lean_ctor_get(v___x_1307_, 4);
v_recordedDeps_1313_ = lean_ctor_get(v___x_1307_, 6);
v_messages_1314_ = lean_ctor_get(v___x_1307_, 7);
v_infoState_1315_ = lean_ctor_get(v___x_1307_, 8);
v_snapshotTasks_1316_ = lean_ctor_get(v___x_1307_, 9);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v___x_1307_, 5);
lean_dec(v_unused_1345_);
v___x_1318_ = v___x_1307_;
v_isShared_1319_ = v_isSharedCheck_1344_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_snapshotTasks_1316_);
lean_inc(v_infoState_1315_);
lean_inc(v_messages_1314_);
lean_inc(v_recordedDeps_1313_);
lean_inc(v_traceState_1312_);
lean_inc(v_auxDeclNGen_1311_);
lean_inc(v_ngen_1310_);
lean_inc(v_nextMacroScope_1309_);
lean_inc(v_env_1308_);
lean_dec(v___x_1307_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1344_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1320_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1321_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1320_, v_env_1308_, v___f_1306_);
v___x_1322_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 5, v___x_1322_);
lean_ctor_set(v___x_1318_, 0, v___x_1321_);
v___x_1324_ = v___x_1318_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_nextMacroScope_1309_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_ngen_1310_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_auxDeclNGen_1311_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_traceState_1312_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1343_, 6, v_recordedDeps_1313_);
lean_ctor_set(v_reuseFailAlloc_1343_, 7, v_messages_1314_);
lean_ctor_set(v_reuseFailAlloc_1343_, 8, v_infoState_1315_);
lean_ctor_set(v_reuseFailAlloc_1343_, 9, v_snapshotTasks_1316_);
v___x_1324_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_mctx_1327_; lean_object* v_zetaDeltaFVarIds_1328_; lean_object* v_postponed_1329_; lean_object* v_diag_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1341_; 
v___x_1325_ = lean_st_ref_put(v___y_1303_, v___x_1324_);
v___x_1326_ = lean_st_ref_take(v___y_1302_);
v_mctx_1327_ = lean_ctor_get(v___x_1326_, 0);
v_zetaDeltaFVarIds_1328_ = lean_ctor_get(v___x_1326_, 2);
v_postponed_1329_ = lean_ctor_get(v___x_1326_, 3);
v_diag_1330_ = lean_ctor_get(v___x_1326_, 4);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1326_, 1);
lean_dec(v_unused_1342_);
v___x_1332_ = v___x_1326_;
v_isShared_1333_ = v_isSharedCheck_1341_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_diag_1330_);
lean_inc(v_postponed_1329_);
lean_inc(v_zetaDeltaFVarIds_1328_);
lean_inc(v_mctx_1327_);
lean_dec(v___x_1326_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1341_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___x_1335_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_mctx_1327_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_zetaDeltaFVarIds_1328_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_postponed_1329_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_diag_1330_);
v___x_1337_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_st_ref_put(v___y_1302_, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1334_);
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint64_t v_h_boxed_1350_; lean_object* v_res_1351_; 
v_h_boxed_1350_ = lean_unbox_uint64(v_h_1346_);
lean_dec_ref(v_h_1346_);
v_res_1351_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1350_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1352_, uint64_t v_k_1353_, lean_object* v_fallback_1354_){
_start:
{
if (lean_obj_tag(v_t_1352_) == 0)
{
lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v_l_1357_; lean_object* v_r_1358_; uint64_t v___x_1359_; uint8_t v___x_1360_; 
v_k_1355_ = lean_ctor_get(v_t_1352_, 1);
v_v_1356_ = lean_ctor_get(v_t_1352_, 2);
v_l_1357_ = lean_ctor_get(v_t_1352_, 3);
v_r_1358_ = lean_ctor_get(v_t_1352_, 4);
v___x_1359_ = lean_unbox_uint64(v_k_1355_);
v___x_1360_ = lean_uint64_dec_lt(v_k_1353_, v___x_1359_);
if (v___x_1360_ == 0)
{
uint64_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = lean_unbox_uint64(v_k_1355_);
v___x_1362_ = lean_uint64_dec_eq(v_k_1353_, v___x_1361_);
if (v___x_1362_ == 0)
{
v_t_1352_ = v_r_1358_;
goto _start;
}
else
{
lean_inc(v_v_1356_);
return v_v_1356_;
}
}
else
{
v_t_1352_ = v_l_1357_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1354_);
return v_fallback_1354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1365_, lean_object* v_k_1366_, lean_object* v_fallback_1367_){
_start:
{
uint64_t v_k_boxed_1368_; lean_object* v_res_1369_; 
v_k_boxed_1368_ = lean_unbox_uint64(v_k_1366_);
lean_dec_ref(v_k_1366_);
v_res_1369_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1365_, v_k_boxed_1368_, v_fallback_1367_);
lean_dec(v_fallback_1367_);
lean_dec(v_t_1365_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1370_, lean_object* v_v_1371_, lean_object* v_t_1372_){
_start:
{
if (lean_obj_tag(v_t_1372_) == 0)
{
lean_object* v_size_1373_; lean_object* v_k_1374_; lean_object* v_v_1375_; lean_object* v_l_1376_; lean_object* v_r_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1661_; 
v_size_1373_ = lean_ctor_get(v_t_1372_, 0);
v_k_1374_ = lean_ctor_get(v_t_1372_, 1);
v_v_1375_ = lean_ctor_get(v_t_1372_, 2);
v_l_1376_ = lean_ctor_get(v_t_1372_, 3);
v_r_1377_ = lean_ctor_get(v_t_1372_, 4);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_t_1372_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1379_ = v_t_1372_;
v_isShared_1380_ = v_isSharedCheck_1661_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_r_1377_);
lean_inc(v_l_1376_);
lean_inc(v_v_1375_);
lean_inc(v_k_1374_);
lean_inc(v_size_1373_);
lean_dec(v_t_1372_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1661_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
uint64_t v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = lean_unbox_uint64(v_k_1374_);
v___x_1382_ = lean_uint64_dec_lt(v_k_1370_, v___x_1381_);
if (v___x_1382_ == 0)
{
uint64_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = lean_unbox_uint64(v_k_1374_);
v___x_1384_ = lean_uint64_dec_eq(v_k_1370_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v_impl_1385_; lean_object* v___x_1386_; 
lean_dec(v_size_1373_);
v_impl_1385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1370_, v_v_1371_, v_r_1377_);
v___x_1386_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1376_) == 0)
{
lean_object* v_size_1387_; lean_object* v_size_1388_; lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v_l_1391_; lean_object* v_r_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_size_1387_ = lean_ctor_get(v_l_1376_, 0);
v_size_1388_ = lean_ctor_get(v_impl_1385_, 0);
v_k_1389_ = lean_ctor_get(v_impl_1385_, 1);
v_v_1390_ = lean_ctor_get(v_impl_1385_, 2);
v_l_1391_ = lean_ctor_get(v_impl_1385_, 3);
lean_inc(v_l_1391_);
v_r_1392_ = lean_ctor_get(v_impl_1385_, 4);
v___x_1393_ = lean_unsigned_to_nat(3u);
v___x_1394_ = lean_nat_mul(v___x_1393_, v_size_1387_);
v___x_1395_ = lean_nat_dec_lt(v___x_1394_, v_size_1388_);
lean_dec(v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_dec(v_l_1391_);
v___x_1396_ = lean_nat_add(v___x_1386_, v_size_1387_);
v___x_1397_ = lean_nat_add(v___x_1396_, v_size_1388_);
lean_dec(v___x_1396_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_impl_1385_);
lean_ctor_set(v___x_1379_, 0, v___x_1397_);
v___x_1399_ = v___x_1379_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_l_1376_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_impl_1385_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1464_; 
lean_inc(v_r_1392_);
lean_inc(v_v_1390_);
lean_inc(v_k_1389_);
lean_inc(v_size_1388_);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_impl_1385_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1465_ = lean_ctor_get(v_impl_1385_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_impl_1385_, 3);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_impl_1385_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_impl_1385_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_impl_1385_, 0);
lean_dec(v_unused_1469_);
v___x_1402_ = v_impl_1385_;
v_isShared_1403_ = v_isSharedCheck_1464_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v_impl_1385_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1464_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_size_1404_; lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v_l_1407_; lean_object* v_r_1408_; lean_object* v_size_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_size_1404_ = lean_ctor_get(v_l_1391_, 0);
v_k_1405_ = lean_ctor_get(v_l_1391_, 1);
v_v_1406_ = lean_ctor_get(v_l_1391_, 2);
v_l_1407_ = lean_ctor_get(v_l_1391_, 3);
v_r_1408_ = lean_ctor_get(v_l_1391_, 4);
v_size_1409_ = lean_ctor_get(v_r_1392_, 0);
v___x_1410_ = lean_unsigned_to_nat(2u);
v___x_1411_ = lean_nat_mul(v___x_1410_, v_size_1409_);
v___x_1412_ = lean_nat_dec_lt(v_size_1404_, v___x_1411_);
lean_dec(v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1440_; 
lean_inc(v_r_1408_);
lean_inc(v_l_1407_);
lean_inc(v_v_1406_);
lean_inc(v_k_1405_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_l_1391_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1441_ = lean_ctor_get(v_l_1391_, 4);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_l_1391_, 3);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_l_1391_, 2);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_l_1391_, 1);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_l_1391_, 0);
lean_dec(v_unused_1445_);
v___x_1414_ = v_l_1391_;
v_isShared_1415_ = v_isSharedCheck_1440_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_l_1391_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1440_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1430_; 
v___x_1416_ = lean_nat_add(v___x_1386_, v_size_1387_);
v___x_1417_ = lean_nat_add(v___x_1416_, v_size_1388_);
lean_dec(v_size_1388_);
if (lean_obj_tag(v_l_1407_) == 0)
{
lean_object* v_size_1438_; 
v_size_1438_ = lean_ctor_get(v_l_1407_, 0);
lean_inc(v_size_1438_);
v___y_1430_ = v_size_1438_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___y_1430_ = v___x_1439_;
goto v___jp_1429_;
}
v___jp_1418_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_nat_add(v___y_1419_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec(v___y_1419_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v_r_1392_);
lean_ctor_set(v___x_1414_, 3, v_r_1408_);
lean_ctor_set(v___x_1414_, 2, v_v_1390_);
lean_ctor_set(v___x_1414_, 1, v_k_1389_);
lean_ctor_set(v___x_1414_, 0, v___x_1422_);
v___x_1424_ = v___x_1414_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_r_1408_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_r_1392_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v___x_1424_);
lean_ctor_set(v___x_1402_, 3, v___y_1420_);
lean_ctor_set(v___x_1402_, 2, v_v_1406_);
lean_ctor_set(v___x_1402_, 1, v_k_1405_);
lean_ctor_set(v___x_1402_, 0, v___x_1417_);
v___x_1426_ = v___x_1402_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___y_1420_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_nat_add(v___x_1416_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec(v___x_1416_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_l_1407_);
lean_ctor_set(v___x_1379_, 0, v___x_1431_);
v___x_1433_ = v___x_1379_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_l_1376_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_l_1407_);
v___x_1433_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_nat_add(v___x_1386_, v_size_1409_);
if (lean_obj_tag(v_r_1408_) == 0)
{
lean_object* v_size_1435_; 
v_size_1435_ = lean_ctor_get(v_r_1408_, 0);
lean_inc(v_size_1435_);
v___y_1419_ = v___x_1434_;
v___y_1420_ = v___x_1433_;
v___y_1421_ = v_size_1435_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___y_1419_ = v___x_1434_;
v___y_1420_ = v___x_1433_;
v___y_1421_ = v___x_1436_;
goto v___jp_1418_;
}
}
}
}
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_del_object(v___x_1379_);
v___x_1446_ = lean_nat_add(v___x_1386_, v_size_1387_);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1388_);
lean_dec(v_size_1388_);
v___x_1448_ = lean_nat_add(v___x_1446_, v_size_1404_);
lean_dec(v___x_1446_);
lean_inc_ref(v_l_1376_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_l_1391_);
lean_ctor_set(v___x_1402_, 3, v_l_1376_);
lean_ctor_set(v___x_1402_, 2, v_v_1375_);
lean_ctor_set(v___x_1402_, 1, v_k_1374_);
lean_ctor_set(v___x_1402_, 0, v___x_1448_);
v___x_1450_ = v___x_1402_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_l_1376_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_l_1391_);
v___x_1450_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_isSharedCheck_1457_ = !lean_is_exclusive(v_l_1376_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; 
v_unused_1458_ = lean_ctor_get(v_l_1376_, 4);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_l_1376_, 3);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_l_1376_, 2);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_l_1376_, 1);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_l_1376_, 0);
lean_dec(v_unused_1462_);
v___x_1452_ = v_l_1376_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v_l_1376_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v_r_1392_);
lean_ctor_set(v___x_1452_, 3, v___x_1450_);
lean_ctor_set(v___x_1452_, 2, v_v_1390_);
lean_ctor_set(v___x_1452_, 1, v_k_1389_);
lean_ctor_set(v___x_1452_, 0, v___x_1447_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_r_1392_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1470_; 
v_l_1470_ = lean_ctor_get(v_impl_1385_, 3);
lean_inc(v_l_1470_);
if (lean_obj_tag(v_l_1470_) == 0)
{
lean_object* v_r_1471_; lean_object* v_k_1472_; lean_object* v_v_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1496_; 
v_r_1471_ = lean_ctor_get(v_impl_1385_, 4);
v_k_1472_ = lean_ctor_get(v_impl_1385_, 1);
v_v_1473_ = lean_ctor_get(v_impl_1385_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_impl_1385_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1497_ = lean_ctor_get(v_impl_1385_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_impl_1385_, 0);
lean_dec(v_unused_1498_);
v___x_1475_ = v_impl_1385_;
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_r_1471_);
lean_inc(v_v_1473_);
lean_inc(v_k_1472_);
lean_dec(v_impl_1385_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1492_; 
v_k_1477_ = lean_ctor_get(v_l_1470_, 1);
v_v_1478_ = lean_ctor_get(v_l_1470_, 2);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_l_1470_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1493_ = lean_ctor_get(v_l_1470_, 4);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1470_, 3);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1470_, 0);
lean_dec(v_unused_1495_);
v___x_1480_ = v_l_1470_;
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_v_1478_);
lean_inc(v_k_1477_);
lean_dec(v_l_1470_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1471_, 2);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v_r_1471_);
lean_ctor_set(v___x_1480_, 3, v_r_1471_);
lean_ctor_set(v___x_1480_, 2, v_v_1375_);
lean_ctor_set(v___x_1480_, 1, v_k_1374_);
lean_ctor_set(v___x_1480_, 0, v___x_1386_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_r_1471_);
v___x_1484_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
lean_inc(v_r_1471_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 3, v_r_1471_);
lean_ctor_set(v___x_1475_, 0, v___x_1386_);
v___x_1486_ = v___x_1475_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1473_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_r_1471_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v___x_1486_);
lean_ctor_set(v___x_1379_, 3, v___x_1484_);
lean_ctor_set(v___x_1379_, 2, v_v_1478_);
lean_ctor_set(v___x_1379_, 1, v_k_1477_);
lean_ctor_set(v___x_1379_, 0, v___x_1482_);
v___x_1488_ = v___x_1379_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
else
{
lean_object* v_r_1499_; 
v_r_1499_ = lean_ctor_get(v_impl_1385_, 4);
lean_inc(v_r_1499_);
if (lean_obj_tag(v_r_1499_) == 0)
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1512_; 
v_k_1500_ = lean_ctor_get(v_impl_1385_, 1);
v_v_1501_ = lean_ctor_get(v_impl_1385_, 2);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_impl_1385_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; 
v_unused_1513_ = lean_ctor_get(v_impl_1385_, 4);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_impl_1385_, 3);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_impl_1385_, 0);
lean_dec(v_unused_1515_);
v___x_1503_ = v_impl_1385_;
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
lean_dec(v_impl_1385_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(3u);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_l_1470_);
lean_ctor_set(v___x_1503_, 2, v_v_1375_);
lean_ctor_set(v___x_1503_, 1, v_k_1374_);
lean_ctor_set(v___x_1503_, 0, v___x_1386_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1470_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1470_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_r_1499_);
lean_ctor_set(v___x_1379_, 3, v___x_1507_);
lean_ctor_set(v___x_1379_, 2, v_v_1501_);
lean_ctor_set(v___x_1379_, 1, v_k_1500_);
lean_ctor_set(v___x_1379_, 0, v___x_1505_);
v___x_1509_ = v___x_1379_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1499_);
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
else
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_unsigned_to_nat(2u);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_impl_1385_);
lean_ctor_set(v___x_1379_, 3, v_r_1499_);
lean_ctor_set(v___x_1379_, 0, v___x_1516_);
v___x_1518_ = v___x_1379_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_r_1499_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_impl_1385_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_dec(v_v_1375_);
lean_dec(v_k_1374_);
v___x_1520_ = lean_box_uint64(v_k_1370_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 2, v_v_1371_);
lean_ctor_set(v___x_1379_, 1, v___x_1520_);
v___x_1522_ = v___x_1379_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_size_1373_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_l_1376_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_r_1377_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_object* v_impl_1524_; lean_object* v___x_1525_; 
lean_dec(v_size_1373_);
v_impl_1524_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1370_, v_v_1371_, v_l_1376_);
v___x_1525_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1377_) == 0)
{
lean_object* v_size_1526_; lean_object* v_size_1527_; lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v_l_1530_; lean_object* v_r_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_size_1526_ = lean_ctor_get(v_r_1377_, 0);
v_size_1527_ = lean_ctor_get(v_impl_1524_, 0);
v_k_1528_ = lean_ctor_get(v_impl_1524_, 1);
v_v_1529_ = lean_ctor_get(v_impl_1524_, 2);
v_l_1530_ = lean_ctor_get(v_impl_1524_, 3);
v_r_1531_ = lean_ctor_get(v_impl_1524_, 4);
lean_inc(v_r_1531_);
v___x_1532_ = lean_unsigned_to_nat(3u);
v___x_1533_ = lean_nat_mul(v___x_1532_, v_size_1526_);
v___x_1534_ = lean_nat_dec_lt(v___x_1533_, v_size_1527_);
lean_dec(v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
lean_dec(v_r_1531_);
v___x_1535_ = lean_nat_add(v___x_1525_, v_size_1527_);
v___x_1536_ = lean_nat_add(v___x_1535_, v_size_1526_);
lean_dec(v___x_1535_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 3, v_impl_1524_);
lean_ctor_set(v___x_1379_, 0, v___x_1536_);
v___x_1538_ = v___x_1379_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1377_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
else
{
lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1605_; 
lean_inc(v_l_1530_);
lean_inc(v_v_1529_);
lean_inc(v_k_1528_);
lean_inc(v_size_1527_);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_impl_1524_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1606_ = lean_ctor_get(v_impl_1524_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_impl_1524_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_impl_1524_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_impl_1524_, 1);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_impl_1524_, 0);
lean_dec(v_unused_1610_);
v___x_1541_ = v_impl_1524_;
v_isShared_1542_ = v_isSharedCheck_1605_;
goto v_resetjp_1540_;
}
else
{
lean_dec(v_impl_1524_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1605_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_size_1543_; lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v_l_1547_; lean_object* v_r_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_size_1543_ = lean_ctor_get(v_l_1530_, 0);
v_size_1544_ = lean_ctor_get(v_r_1531_, 0);
v_k_1545_ = lean_ctor_get(v_r_1531_, 1);
v_v_1546_ = lean_ctor_get(v_r_1531_, 2);
v_l_1547_ = lean_ctor_get(v_r_1531_, 3);
v_r_1548_ = lean_ctor_get(v_r_1531_, 4);
v___x_1549_ = lean_unsigned_to_nat(2u);
v___x_1550_ = lean_nat_mul(v___x_1549_, v_size_1543_);
v___x_1551_ = lean_nat_dec_lt(v_size_1544_, v___x_1550_);
lean_dec(v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1580_; 
lean_inc(v_r_1548_);
lean_inc(v_l_1547_);
lean_inc(v_v_1546_);
lean_inc(v_k_1545_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_r_1531_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; lean_object* v_unused_1585_; 
v_unused_1581_ = lean_ctor_get(v_r_1531_, 4);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_r_1531_, 3);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_r_1531_, 2);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_r_1531_, 1);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_r_1531_, 0);
lean_dec(v_unused_1585_);
v___x_1553_ = v_r_1531_;
v_isShared_1554_ = v_isSharedCheck_1580_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v_r_1531_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1580_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___x_1568_; lean_object* v___y_1570_; 
v___x_1555_ = lean_nat_add(v___x_1525_, v_size_1527_);
lean_dec(v_size_1527_);
v___x_1556_ = lean_nat_add(v___x_1555_, v_size_1526_);
lean_dec(v___x_1555_);
v___x_1568_ = lean_nat_add(v___x_1525_, v_size_1543_);
if (lean_obj_tag(v_l_1547_) == 0)
{
lean_object* v_size_1578_; 
v_size_1578_ = lean_ctor_get(v_l_1547_, 0);
lean_inc(v_size_1578_);
v___y_1570_ = v_size_1578_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___y_1570_ = v___x_1579_;
goto v___jp_1569_;
}
v___jp_1557_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_nat_add(v___y_1558_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec(v___y_1558_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_r_1377_);
lean_ctor_set(v___x_1553_, 3, v_r_1548_);
lean_ctor_set(v___x_1553_, 2, v_v_1375_);
lean_ctor_set(v___x_1553_, 1, v_k_1374_);
lean_ctor_set(v___x_1553_, 0, v___x_1561_);
v___x_1563_ = v___x_1553_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_r_1548_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_r_1377_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 4, v___x_1563_);
lean_ctor_set(v___x_1541_, 3, v___y_1559_);
lean_ctor_set(v___x_1541_, 2, v_v_1546_);
lean_ctor_set(v___x_1541_, 1, v_k_1545_);
lean_ctor_set(v___x_1541_, 0, v___x_1556_);
v___x_1565_ = v___x_1541_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1545_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1546_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v___y_1559_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
v___jp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_nat_add(v___x_1568_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec(v___x_1568_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_l_1547_);
lean_ctor_set(v___x_1379_, 3, v_l_1530_);
lean_ctor_set(v___x_1379_, 2, v_v_1529_);
lean_ctor_set(v___x_1379_, 1, v_k_1528_);
lean_ctor_set(v___x_1379_, 0, v___x_1571_);
v___x_1573_ = v___x_1379_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_l_1530_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_l_1547_);
v___x_1573_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_nat_add(v___x_1525_, v_size_1526_);
if (lean_obj_tag(v_r_1548_) == 0)
{
lean_object* v_size_1575_; 
v_size_1575_ = lean_ctor_get(v_r_1548_, 0);
lean_inc(v_size_1575_);
v___y_1558_ = v___x_1574_;
v___y_1559_ = v___x_1573_;
v___y_1560_ = v_size_1575_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___y_1558_ = v___x_1574_;
v___y_1559_ = v___x_1573_;
v___y_1560_ = v___x_1576_;
goto v___jp_1557_;
}
}
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_del_object(v___x_1379_);
v___x_1586_ = lean_nat_add(v___x_1525_, v_size_1527_);
lean_dec(v_size_1527_);
v___x_1587_ = lean_nat_add(v___x_1586_, v_size_1526_);
lean_dec(v___x_1586_);
v___x_1588_ = lean_nat_add(v___x_1525_, v_size_1526_);
v___x_1589_ = lean_nat_add(v___x_1588_, v_size_1544_);
lean_dec(v___x_1588_);
lean_inc_ref(v_r_1377_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 4, v_r_1377_);
lean_ctor_set(v___x_1541_, 3, v_r_1531_);
lean_ctor_set(v___x_1541_, 2, v_v_1375_);
lean_ctor_set(v___x_1541_, 1, v_k_1374_);
lean_ctor_set(v___x_1541_, 0, v___x_1589_);
v___x_1591_ = v___x_1541_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_r_1531_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_r_1377_);
v___x_1591_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_isSharedCheck_1598_ = !lean_is_exclusive(v_r_1377_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; lean_object* v_unused_1603_; 
v_unused_1599_ = lean_ctor_get(v_r_1377_, 4);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_r_1377_, 3);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_r_1377_, 2);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_r_1377_, 1);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_r_1377_, 0);
lean_dec(v_unused_1603_);
v___x_1593_ = v_r_1377_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v_r_1377_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v___x_1591_);
lean_ctor_set(v___x_1593_, 3, v_l_1530_);
lean_ctor_set(v___x_1593_, 2, v_v_1529_);
lean_ctor_set(v___x_1593_, 1, v_k_1528_);
lean_ctor_set(v___x_1593_, 0, v___x_1587_);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_l_1530_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v___x_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1611_; 
v_l_1611_ = lean_ctor_get(v_impl_1524_, 3);
if (lean_obj_tag(v_l_1611_) == 0)
{
lean_object* v_r_1612_; lean_object* v_k_1613_; lean_object* v_v_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1625_; 
lean_inc_ref(v_l_1611_);
v_r_1612_ = lean_ctor_get(v_impl_1524_, 4);
v_k_1613_ = lean_ctor_get(v_impl_1524_, 1);
v_v_1614_ = lean_ctor_get(v_impl_1524_, 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_impl_1524_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; lean_object* v_unused_1627_; 
v_unused_1626_ = lean_ctor_get(v_impl_1524_, 3);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_impl_1524_, 0);
lean_dec(v_unused_1627_);
v___x_1616_ = v_impl_1524_;
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_r_1612_);
lean_inc(v_v_1614_);
lean_inc(v_k_1613_);
lean_dec(v_impl_1524_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1612_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 3, v_r_1612_);
lean_ctor_set(v___x_1616_, 2, v_v_1375_);
lean_ctor_set(v___x_1616_, 1, v_k_1374_);
lean_ctor_set(v___x_1616_, 0, v___x_1525_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_r_1612_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_r_1612_);
v___x_1620_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1622_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v___x_1620_);
lean_ctor_set(v___x_1379_, 3, v_l_1611_);
lean_ctor_set(v___x_1379_, 2, v_v_1614_);
lean_ctor_set(v___x_1379_, 1, v_k_1613_);
lean_ctor_set(v___x_1379_, 0, v___x_1618_);
v___x_1622_ = v___x_1379_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1613_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1614_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_l_1611_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_r_1628_; 
v_r_1628_ = lean_ctor_get(v_impl_1524_, 4);
lean_inc(v_r_1628_);
if (lean_obj_tag(v_r_1628_) == 0)
{
lean_object* v_k_1629_; lean_object* v_v_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1653_; 
lean_inc(v_l_1611_);
v_k_1629_ = lean_ctor_get(v_impl_1524_, 1);
v_v_1630_ = lean_ctor_get(v_impl_1524_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_impl_1524_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; 
v_unused_1654_ = lean_ctor_get(v_impl_1524_, 4);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_impl_1524_, 3);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_impl_1524_, 0);
lean_dec(v_unused_1656_);
v___x_1632_ = v_impl_1524_;
v_isShared_1633_ = v_isSharedCheck_1653_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_v_1630_);
lean_inc(v_k_1629_);
lean_dec(v_impl_1524_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1653_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1649_; 
v_k_1634_ = lean_ctor_get(v_r_1628_, 1);
v_v_1635_ = lean_ctor_get(v_r_1628_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_r_1628_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1650_ = lean_ctor_get(v_r_1628_, 4);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_r_1628_, 3);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_r_1628_, 0);
lean_dec(v_unused_1652_);
v___x_1637_ = v_r_1628_;
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_v_1635_);
lean_inc(v_k_1634_);
lean_dec(v_r_1628_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(3u);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v_l_1611_);
lean_ctor_set(v___x_1637_, 3, v_l_1611_);
lean_ctor_set(v___x_1637_, 2, v_v_1630_);
lean_ctor_set(v___x_1637_, 1, v_k_1629_);
lean_ctor_set(v___x_1637_, 0, v___x_1525_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_k_1629_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_v_1630_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_l_1611_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_l_1611_);
v___x_1641_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 4, v_l_1611_);
lean_ctor_set(v___x_1632_, 2, v_v_1375_);
lean_ctor_set(v___x_1632_, 1, v_k_1374_);
lean_ctor_set(v___x_1632_, 0, v___x_1525_);
v___x_1643_ = v___x_1632_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_l_1611_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_l_1611_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v___x_1643_);
lean_ctor_set(v___x_1379_, 3, v___x_1641_);
lean_ctor_set(v___x_1379_, 2, v_v_1635_);
lean_ctor_set(v___x_1379_, 1, v_k_1634_);
lean_ctor_set(v___x_1379_, 0, v___x_1639_);
v___x_1645_ = v___x_1379_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1634_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_unsigned_to_nat(2u);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_r_1628_);
lean_ctor_set(v___x_1379_, 3, v_impl_1524_);
lean_ctor_set(v___x_1379_, 0, v___x_1657_);
v___x_1659_ = v___x_1379_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1628_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_box_uint64(v_k_1370_);
v___x_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
lean_ctor_set(v___x_1664_, 2, v_v_1371_);
lean_ctor_set(v___x_1664_, 3, v_t_1372_);
lean_ctor_set(v___x_1664_, 4, v_t_1372_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1665_, lean_object* v_v_1666_, lean_object* v_t_1667_){
_start:
{
uint64_t v_k_boxed_1668_; lean_object* v_res_1669_; 
v_k_boxed_1668_ = lean_unbox_uint64(v_k_1665_);
lean_dec_ref(v_k_1665_);
v_res_1669_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1668_, v_v_1666_, v_t_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1670_, lean_object* v_s_1671_){
_start:
{
uint64_t v_javascriptHash_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_javascriptHash_1672_ = lean_ctor_get_uint64(v_wi_1670_, sizeof(void*)*2);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_wi_1670_);
v___x_1674_ = lean_box(0);
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1671_, v_javascriptHash_1672_, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1673_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1672_, v___x_1676_, v_s_1671_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___f_1682_; lean_object* v___x_1683_; lean_object* v_env_1684_; lean_object* v_nextMacroScope_1685_; lean_object* v_ngen_1686_; lean_object* v_auxDeclNGen_1687_; lean_object* v_traceState_1688_; lean_object* v_recordedDeps_1689_; lean_object* v_messages_1690_; lean_object* v_infoState_1691_; lean_object* v_snapshotTasks_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1720_; 
v___f_1682_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1682_, 0, v_wi_1678_);
v___x_1683_ = lean_st_ref_take(v___y_1680_);
v_env_1684_ = lean_ctor_get(v___x_1683_, 0);
v_nextMacroScope_1685_ = lean_ctor_get(v___x_1683_, 1);
v_ngen_1686_ = lean_ctor_get(v___x_1683_, 2);
v_auxDeclNGen_1687_ = lean_ctor_get(v___x_1683_, 3);
v_traceState_1688_ = lean_ctor_get(v___x_1683_, 4);
v_recordedDeps_1689_ = lean_ctor_get(v___x_1683_, 6);
v_messages_1690_ = lean_ctor_get(v___x_1683_, 7);
v_infoState_1691_ = lean_ctor_get(v___x_1683_, 8);
v_snapshotTasks_1692_ = lean_ctor_get(v___x_1683_, 9);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v___x_1683_, 5);
lean_dec(v_unused_1721_);
v___x_1694_ = v___x_1683_;
v_isShared_1695_ = v_isSharedCheck_1720_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_snapshotTasks_1692_);
lean_inc(v_infoState_1691_);
lean_inc(v_messages_1690_);
lean_inc(v_recordedDeps_1689_);
lean_inc(v_traceState_1688_);
lean_inc(v_auxDeclNGen_1687_);
lean_inc(v_ngen_1686_);
lean_inc(v_nextMacroScope_1685_);
lean_inc(v_env_1684_);
lean_dec(v___x_1683_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1720_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1696_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1697_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1696_, v_env_1684_, v___f_1682_);
v___x_1698_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 5, v___x_1698_);
lean_ctor_set(v___x_1694_, 0, v___x_1697_);
v___x_1700_ = v___x_1694_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_nextMacroScope_1685_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_ngen_1686_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_auxDeclNGen_1687_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_traceState_1688_);
lean_ctor_set(v_reuseFailAlloc_1719_, 5, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1719_, 6, v_recordedDeps_1689_);
lean_ctor_set(v_reuseFailAlloc_1719_, 7, v_messages_1690_);
lean_ctor_set(v_reuseFailAlloc_1719_, 8, v_infoState_1691_);
lean_ctor_set(v_reuseFailAlloc_1719_, 9, v_snapshotTasks_1692_);
v___x_1700_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_mctx_1703_; lean_object* v_zetaDeltaFVarIds_1704_; lean_object* v_postponed_1705_; lean_object* v_diag_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1717_; 
v___x_1701_ = lean_st_ref_put(v___y_1680_, v___x_1700_);
v___x_1702_ = lean_st_ref_take(v___y_1679_);
v_mctx_1703_ = lean_ctor_get(v___x_1702_, 0);
v_zetaDeltaFVarIds_1704_ = lean_ctor_get(v___x_1702_, 2);
v_postponed_1705_ = lean_ctor_get(v___x_1702_, 3);
v_diag_1706_ = lean_ctor_get(v___x_1702_, 4);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v___x_1702_, 1);
lean_dec(v_unused_1718_);
v___x_1708_ = v___x_1702_;
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_diag_1706_);
lean_inc(v_postponed_1705_);
lean_inc(v_zetaDeltaFVarIds_1704_);
lean_inc(v_mctx_1703_);
lean_dec(v___x_1702_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___x_1711_);
v___x_1713_ = v___x_1708_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_mctx_1703_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_zetaDeltaFVarIds_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_postponed_1705_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_diag_1706_);
v___x_1713_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_st_ref_put(v___y_1679_, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1710_);
return v___x_1715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(lean_object* v_ext_1727_, lean_object* v_b_1728_, uint8_t v_kind_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_toCold_1734_; lean_object* v_currNamespace_1735_; lean_object* v___x_1736_; lean_object* v_env_1737_; lean_object* v_nextMacroScope_1738_; lean_object* v_ngen_1739_; lean_object* v_auxDeclNGen_1740_; lean_object* v_traceState_1741_; lean_object* v_recordedDeps_1742_; lean_object* v_messages_1743_; lean_object* v_infoState_1744_; lean_object* v_snapshotTasks_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1772_; 
v_toCold_1734_ = lean_ctor_get(v___y_1731_, 0);
v_currNamespace_1735_ = lean_ctor_get(v_toCold_1734_, 4);
v___x_1736_ = lean_st_ref_take(v___y_1732_);
v_env_1737_ = lean_ctor_get(v___x_1736_, 0);
v_nextMacroScope_1738_ = lean_ctor_get(v___x_1736_, 1);
v_ngen_1739_ = lean_ctor_get(v___x_1736_, 2);
v_auxDeclNGen_1740_ = lean_ctor_get(v___x_1736_, 3);
v_traceState_1741_ = lean_ctor_get(v___x_1736_, 4);
v_recordedDeps_1742_ = lean_ctor_get(v___x_1736_, 6);
v_messages_1743_ = lean_ctor_get(v___x_1736_, 7);
v_infoState_1744_ = lean_ctor_get(v___x_1736_, 8);
v_snapshotTasks_1745_ = lean_ctor_get(v___x_1736_, 9);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1736_, 5);
lean_dec(v_unused_1773_);
v___x_1747_ = v___x_1736_;
v_isShared_1748_ = v_isSharedCheck_1772_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snapshotTasks_1745_);
lean_inc(v_infoState_1744_);
lean_inc(v_messages_1743_);
lean_inc(v_recordedDeps_1742_);
lean_inc(v_traceState_1741_);
lean_inc(v_auxDeclNGen_1740_);
lean_inc(v_ngen_1739_);
lean_inc(v_nextMacroScope_1738_);
lean_inc(v_env_1737_);
lean_dec(v___x_1736_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1772_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_inc(v_currNamespace_1735_);
v___x_1749_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1737_, v_ext_1727_, v_b_1728_, v_kind_1729_, v_currNamespace_1735_);
v___x_1750_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 5, v___x_1750_);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_nextMacroScope_1738_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_ngen_1739_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_auxDeclNGen_1740_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_traceState_1741_);
lean_ctor_set(v_reuseFailAlloc_1771_, 5, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1771_, 6, v_recordedDeps_1742_);
lean_ctor_set(v_reuseFailAlloc_1771_, 7, v_messages_1743_);
lean_ctor_set(v_reuseFailAlloc_1771_, 8, v_infoState_1744_);
lean_ctor_set(v_reuseFailAlloc_1771_, 9, v_snapshotTasks_1745_);
v___x_1752_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_mctx_1755_; lean_object* v_zetaDeltaFVarIds_1756_; lean_object* v_postponed_1757_; lean_object* v_diag_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1769_; 
v___x_1753_ = lean_st_ref_put(v___y_1732_, v___x_1752_);
v___x_1754_ = lean_st_ref_take(v___y_1730_);
v_mctx_1755_ = lean_ctor_get(v___x_1754_, 0);
v_zetaDeltaFVarIds_1756_ = lean_ctor_get(v___x_1754_, 2);
v_postponed_1757_ = lean_ctor_get(v___x_1754_, 3);
v_diag_1758_ = lean_ctor_get(v___x_1754_, 4);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1754_, 1);
lean_dec(v_unused_1770_);
v___x_1760_ = v___x_1754_;
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_diag_1758_);
lean_inc(v_postponed_1757_);
lean_inc(v_zetaDeltaFVarIds_1756_);
lean_inc(v_mctx_1755_);
lean_dec(v___x_1754_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v___x_1763_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_mctx_1755_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_zetaDeltaFVarIds_1756_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_postponed_1757_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_diag_1758_);
v___x_1765_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_st_ref_put(v___y_1730_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1762_);
return v___x_1767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg___boxed(lean_object* v_ext_1774_, lean_object* v_b_1775_, lean_object* v_kind_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v_kind_boxed_1781_; lean_object* v_res_1782_; 
v_kind_boxed_1781_ = lean_unbox(v_kind_1776_);
v_res_1782_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v_ext_1774_, v_b_1775_, v_kind_boxed_1781_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1783_, lean_object* v_n_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1793_ = lean_box_uint64(v_h_1783_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v_n_1784_);
v___x_1795_ = 2;
v___x_1796_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v___x_1792_, v___x_1794_, v___x_1795_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1797_, lean_object* v_n_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
uint64_t v_h_boxed_1806_; lean_object* v_res_1807_; 
v_h_boxed_1806_ = lean_unbox_uint64(v_h_1797_);
lean_dec_ref(v_h_1797_);
v_res_1807_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1806_, v_n_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1808_, lean_object* v_n_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1817_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1818_ = lean_box_uint64(v_h_1808_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v_n_1809_);
v___x_1820_ = 0;
v___x_1821_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v___x_1817_, v___x_1819_, v___x_1820_, v___y_1813_, v___y_1814_, v___y_1815_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1822_, lean_object* v_n_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
uint64_t v_h_boxed_1831_; lean_object* v_res_1832_; 
v_h_boxed_1831_ = lean_unbox_uint64(v_h_1822_);
lean_dec_ref(v_h_1822_);
v_res_1832_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1831_, v_n_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_1833_, lean_object* v___y_1834_){
_start:
{
if (lean_obj_tag(v_x_1833_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1836_; 
v_a_1835_ = lean_ctor_get(v_x_1833_, 0);
lean_inc(v_a_1835_);
v___x_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1835_);
lean_ctor_set(v___x_1836_, 1, v___y_1834_);
return v___x_1836_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v_x_1833_, 0);
lean_inc(v_a_1837_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_a_1837_);
lean_ctor_set(v___x_1838_, 1, v___y_1834_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_1839_, v___y_1840_);
lean_dec_ref(v_x_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1842_, lean_object* v_stx_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1842_, v_stx_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
if (lean_obj_tag(v_a_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_a_1848_ = lean_ctor_get(v___x_1846_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1846_, 0);
lean_dec(v_unused_1857_);
v___x_1850_ = v___x_1846_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1846_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_a_1848_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_val_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1886_; 
v_val_1858_ = lean_ctor_get(v_a_1847_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1847_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1860_ = v_a_1847_;
v_isShared_1861_ = v_isSharedCheck_1886_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_val_1858_);
lean_dec(v_a_1847_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1886_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_snd_1862_; 
v_snd_1862_ = lean_ctor_get(v_val_1858_, 1);
lean_inc(v_snd_1862_);
lean_dec(v_val_1858_);
if (lean_obj_tag(v_snd_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1860_);
v_a_1863_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1846_, 2);
v_a_1864_ = lean_ctor_get(v_snd_1862_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_snd_1862_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1866_ = v_snd_1862_;
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v_snd_1862_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1869_, v_a_1863_);
lean_dec_ref(v___x_1869_);
return v___x_1870_;
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1885_; 
v_a_1873_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1846_, 2);
v_a_1874_ = lean_ctor_get(v_snd_1862_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_snd_1862_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1876_ = v_snd_1862_;
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v_snd_1862_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v_a_1874_);
v___x_1879_ = v___x_1860_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_1881_, v_a_1873_);
lean_dec_ref(v___x_1881_);
return v___x_1882_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1846_, 0);
v_a_1888_ = lean_ctor_get(v___x_1846_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1846_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_inc(v_a_1887_);
lean_dec(v___x_1846_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1896_, lean_object* v_stx_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1896_, v_stx_1897_, v___y_1898_, v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; lean_object* v_env_1908_; uint8_t v___x_1909_; lean_object* v_env_1910_; lean_object* v___x_1911_; lean_object* v_toCold_1912_; lean_object* v_mctx_1913_; lean_object* v_lctx_1914_; lean_object* v_options_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1907_ = lean_st_ref_get(v___y_1905_);
v_env_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_ref(v_env_1908_);
lean_dec(v___x_1907_);
v___x_1909_ = 0;
v_env_1910_ = l_Lean_Environment_setRecordingDeps(v_env_1908_, v___x_1909_);
v___x_1911_ = lean_st_ref_get(v___y_1903_);
v_toCold_1912_ = lean_ctor_get(v___y_1904_, 0);
v_mctx_1913_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_ref(v_mctx_1913_);
lean_dec(v___x_1911_);
v_lctx_1914_ = lean_ctor_get(v___y_1902_, 2);
v_options_1915_ = lean_ctor_get(v_toCold_1912_, 2);
lean_inc_ref(v_options_1915_);
lean_inc_ref(v_lctx_1914_);
v___x_1916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1916_, 0, v_env_1910_);
lean_ctor_set(v___x_1916_, 1, v_mctx_1913_);
lean_ctor_set(v___x_1916_, 2, v_lctx_1914_);
lean_ctor_set(v___x_1916_, 3, v_options_1915_);
v___x_1917_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v_msgData_1901_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1926_; double v___x_1927_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_float_of_nat(v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1930_, lean_object* v_msg_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_ref_1937_; lean_object* v___x_1938_; lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1984_; 
v_ref_1937_ = lean_ctor_get(v___y_1934_, 2);
v___x_1938_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msg_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1984_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1984_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v_traceState_1944_; lean_object* v_env_1945_; lean_object* v_nextMacroScope_1946_; lean_object* v_ngen_1947_; lean_object* v_auxDeclNGen_1948_; lean_object* v_cache_1949_; lean_object* v_recordedDeps_1950_; lean_object* v_messages_1951_; lean_object* v_infoState_1952_; lean_object* v_snapshotTasks_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1983_; 
v___x_1943_ = lean_st_ref_take(v___y_1935_);
v_traceState_1944_ = lean_ctor_get(v___x_1943_, 4);
v_env_1945_ = lean_ctor_get(v___x_1943_, 0);
v_nextMacroScope_1946_ = lean_ctor_get(v___x_1943_, 1);
v_ngen_1947_ = lean_ctor_get(v___x_1943_, 2);
v_auxDeclNGen_1948_ = lean_ctor_get(v___x_1943_, 3);
v_cache_1949_ = lean_ctor_get(v___x_1943_, 5);
v_recordedDeps_1950_ = lean_ctor_get(v___x_1943_, 6);
v_messages_1951_ = lean_ctor_get(v___x_1943_, 7);
v_infoState_1952_ = lean_ctor_get(v___x_1943_, 8);
v_snapshotTasks_1953_ = lean_ctor_get(v___x_1943_, 9);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1955_ = v___x_1943_;
v_isShared_1956_ = v_isSharedCheck_1983_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_snapshotTasks_1953_);
lean_inc(v_infoState_1952_);
lean_inc(v_messages_1951_);
lean_inc(v_recordedDeps_1950_);
lean_inc(v_cache_1949_);
lean_inc(v_traceState_1944_);
lean_inc(v_auxDeclNGen_1948_);
lean_inc(v_ngen_1947_);
lean_inc(v_nextMacroScope_1946_);
lean_inc(v_env_1945_);
lean_dec(v___x_1943_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1983_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
uint64_t v_tid_1957_; lean_object* v_traces_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1982_; 
v_tid_1957_ = lean_ctor_get_uint64(v_traceState_1944_, sizeof(void*)*1);
v_traces_1958_ = lean_ctor_get(v_traceState_1944_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_traceState_1944_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1960_ = v_traceState_1944_;
v_isShared_1961_ = v_isSharedCheck_1982_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_traces_1958_);
lean_dec(v_traceState_1944_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1982_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; double v___x_1964_; uint8_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1965_ = 0;
v___x_1966_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1967_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1967_, 0, v_cls_1930_);
lean_ctor_set(v___x_1967_, 1, v___x_1963_);
lean_ctor_set(v___x_1967_, 2, v___x_1966_);
lean_ctor_set_float(v___x_1967_, sizeof(void*)*3, v___x_1964_);
lean_ctor_set_float(v___x_1967_, sizeof(void*)*3 + 8, v___x_1964_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*3 + 16, v___x_1965_);
v___x_1968_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1969_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v_a_1939_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
lean_inc(v_ref_1937_);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_ref_1937_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l_Lean_PersistentArray_push___redArg(v_traces_1958_, v___x_1970_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1971_);
v___x_1973_ = v___x_1960_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1971_);
lean_ctor_set_uint64(v_reuseFailAlloc_1981_, sizeof(void*)*1, v_tid_1957_);
v___x_1973_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 4, v___x_1973_);
v___x_1975_ = v___x_1955_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_env_1945_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_nextMacroScope_1946_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_ngen_1947_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_auxDeclNGen_1948_);
lean_ctor_set(v_reuseFailAlloc_1980_, 4, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1980_, 5, v_cache_1949_);
lean_ctor_set(v_reuseFailAlloc_1980_, 6, v_recordedDeps_1950_);
lean_ctor_set(v_reuseFailAlloc_1980_, 7, v_messages_1951_);
lean_ctor_set(v_reuseFailAlloc_1980_, 8, v_infoState_1952_);
lean_ctor_set(v_reuseFailAlloc_1980_, 9, v_snapshotTasks_1953_);
v___x_1975_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_st_ref_put(v___y_1935_, v___x_1975_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1962_);
v___x_1978_ = v___x_1941_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1962_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1985_, lean_object* v_msg_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1985_, v_msg_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
if (lean_obj_tag(v_as_1996_) == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
else
{
lean_object* v_toCold_2006_; lean_object* v_options_2007_; uint8_t v_hasTrace_2008_; 
v_toCold_2006_ = lean_ctor_get(v___y_2001_, 0);
v_options_2007_ = lean_ctor_get(v_toCold_2006_, 2);
v_hasTrace_2008_ = lean_ctor_get_uint8(v_options_2007_, sizeof(void*)*1);
if (v_hasTrace_2008_ == 0)
{
lean_object* v_tail_2009_; 
v_tail_2009_ = lean_ctor_get(v_as_1996_, 1);
lean_inc(v_tail_2009_);
lean_dec_ref_known(v_as_1996_, 2);
v_as_1996_ = v_tail_2009_;
goto _start;
}
else
{
lean_object* v_head_2011_; lean_object* v_tail_2012_; lean_object* v_fst_2013_; lean_object* v_snd_2014_; lean_object* v_inheritedTraceOptions_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_head_2011_ = lean_ctor_get(v_as_1996_, 0);
lean_inc(v_head_2011_);
v_tail_2012_ = lean_ctor_get(v_as_1996_, 1);
lean_inc(v_tail_2012_);
lean_dec_ref_known(v_as_1996_, 2);
v_fst_2013_ = lean_ctor_get(v_head_2011_, 0);
lean_inc_n(v_fst_2013_, 2);
v_snd_2014_ = lean_ctor_get(v_head_2011_, 1);
lean_inc(v_snd_2014_);
lean_dec(v_head_2011_);
v_inheritedTraceOptions_2015_ = lean_ctor_get(v_toCold_2006_, 11);
v___x_2016_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2017_ = l_Lean_Name_append(v___x_2016_, v_fst_2013_);
v___x_2018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2015_, v_options_2007_, v___x_2017_);
lean_dec(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_dec(v_snd_2014_);
lean_dec(v_fst_2013_);
v_as_1996_ = v_tail_2012_;
goto _start;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_snd_2014_);
v___x_2021_ = l_Lean_MessageData_ofFormat(v___x_2020_);
v___x_2022_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_2013_, v___x_2021_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref_known(v___x_2022_, 1);
v_as_1996_ = v_tail_2012_;
goto _start;
}
else
{
lean_dec(v_tail_2012_);
return v___x_2022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_currNamespace_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v_currNamespace_2033_);
lean_ctor_set(v___x_2036_, 1, v___y_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_currNamespace_2037_, v___y_2038_, v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(lean_object* v_opts_2041_, lean_object* v_opt_2042_){
_start:
{
lean_object* v_name_2043_; lean_object* v_defValue_2044_; lean_object* v_map_2045_; lean_object* v___x_2046_; 
v_name_2043_ = lean_ctor_get(v_opt_2042_, 0);
v_defValue_2044_ = lean_ctor_get(v_opt_2042_, 1);
v_map_2045_ = lean_ctor_get(v_opts_2041_, 0);
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2045_, v_name_2043_);
if (lean_obj_tag(v___x_2046_) == 0)
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_unbox(v_defValue_2044_);
return v___x_2047_;
}
else
{
lean_object* v_val_2048_; 
v_val_2048_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v___x_2046_, 1);
if (lean_obj_tag(v_val_2048_) == 1)
{
uint8_t v_v_2049_; 
v_v_2049_ = lean_ctor_get_uint8(v_val_2048_, 0);
lean_dec_ref_known(v_val_2048_, 0);
return v_v_2049_;
}
else
{
uint8_t v___x_2050_; 
lean_dec(v_val_2048_);
v___x_2050_ = lean_unbox(v_defValue_2044_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___boxed(lean_object* v_opts_2051_, lean_object* v_opt_2052_){
_start:
{
uint8_t v_res_2053_; lean_object* v_r_2054_; 
v_res_2053_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(v_opts_2051_, v_opt_2052_);
lean_dec_ref(v_opt_2052_);
lean_dec_ref(v_opts_2051_);
v_r_2054_ = lean_box(v_res_2053_);
return v_r_2054_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_box(1);
v___x_2056_ = l_Lean_MessageData_ofFormat(v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__2));
v___x_2061_ = l_Lean_MessageData_ofFormat(v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24(lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
return v_x_2062_;
}
else
{
lean_object* v_head_2064_; lean_object* v_tail_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2087_; 
v_head_2064_ = lean_ctor_get(v_x_2063_, 0);
v_tail_2065_ = lean_ctor_get(v_x_2063_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2067_ = v_x_2063_;
v_isShared_2068_ = v_isSharedCheck_2087_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_tail_2065_);
lean_inc(v_head_2064_);
lean_dec(v_x_2063_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2087_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_before_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2085_; 
v_before_2069_ = lean_ctor_get(v_head_2064_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_head_2064_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v_head_2064_, 1);
lean_dec(v_unused_2086_);
v___x_2071_ = v_head_2064_;
v_isShared_2072_ = v_isSharedCheck_2085_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_before_2069_);
lean_dec(v_head_2064_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2085_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0);
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 7);
lean_ctor_set(v___x_2071_, 1, v___x_2073_);
lean_ctor_set(v___x_2071_, 0, v_x_2062_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_x_2062_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__3);
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 7);
lean_ctor_set(v___x_2067_, 1, v___x_2076_);
lean_ctor_set(v___x_2067_, 0, v___x_2075_);
v___x_2078_ = v___x_2067_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = l_Lean_MessageData_ofSyntax(v_before_2069_);
v___x_2080_ = l_Lean_indentD(v___x_2079_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v_x_2062_ = v___x_2081_;
v_x_2063_ = v_tail_2065_;
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
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__1));
v___x_2092_ = l_Lean_MessageData_ofFormat(v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(lean_object* v_msgData_2093_, lean_object* v_macroStack_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2095_);
v___x_2098_ = l_Lean_Elab_pp_macroStack;
v___x_2099_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(v___x_2097_, v___x_2098_);
lean_dec_ref(v___x_2097_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec(v_macroStack_2094_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_msgData_2093_);
return v___x_2100_;
}
else
{
if (lean_obj_tag(v_macroStack_2094_) == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_msgData_2093_);
return v___x_2101_;
}
else
{
lean_object* v_head_2102_; lean_object* v_after_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2118_; 
v_head_2102_ = lean_ctor_get(v_macroStack_2094_, 0);
lean_inc(v_head_2102_);
v_after_2103_ = lean_ctor_get(v_head_2102_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_head_2102_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_head_2102_, 0);
lean_dec(v_unused_2119_);
v___x_2105_ = v_head_2102_;
v_isShared_2106_ = v_isSharedCheck_2118_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_after_2103_);
lean_dec(v_head_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2118_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24___closed__0);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 7);
lean_ctor_set(v___x_2105_, 1, v___x_2107_);
lean_ctor_set(v___x_2105_, 0, v_msgData_2093_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_msgData_2093_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_msgData_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2110_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = l_Lean_MessageData_ofSyntax(v_after_2103_);
v___x_2113_ = l_Lean_indentD(v___x_2112_);
v_msgData_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2114_, 0, v___x_2111_);
lean_ctor_set(v_msgData_2114_, 1, v___x_2113_);
v___x_2115_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__24(v_msgData_2114_, v_macroStack_2094_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___boxed(lean_object* v_msgData_2120_, lean_object* v_macroStack_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_msgData_2120_, v_macroStack_2121_, v___y_2122_);
lean_dec_ref(v___y_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_ref_2133_; lean_object* v_macroStack_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2147_; 
v_ref_2133_ = lean_ctor_get(v___y_2130_, 2);
v_macroStack_2134_ = lean_ctor_get(v___y_2126_, 1);
v___x_2135_ = l_Lean_Elab_getBetterRef(v_ref_2133_, v_macroStack_2134_);
v___x_2136_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msg_2125_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
lean_inc(v_macroStack_2134_);
v___x_2138_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_a_2137_, v_macroStack_2134_, v___y_2130_);
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2135_);
lean_ctor_set(v___x_2143_, 1, v_a_2139_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 1);
lean_ctor_set(v___x_2141_, 0, v___x_2143_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2157_, lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_toCold_2166_; lean_object* v_currRecDepth_2167_; lean_object* v_ref_2168_; uint16_t v_optionFlags_2169_; uint8_t v_suppressElabErrors_2170_; uint8_t v_checkDeprecated_2171_; uint8_t v_isRecordingDeps_2172_; lean_object* v_ref_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_toCold_2166_ = lean_ctor_get(v___y_2163_, 0);
v_currRecDepth_2167_ = lean_ctor_get(v___y_2163_, 1);
v_ref_2168_ = lean_ctor_get(v___y_2163_, 2);
v_optionFlags_2169_ = lean_ctor_get_uint16(v___y_2163_, sizeof(void*)*3);
v_suppressElabErrors_2170_ = lean_ctor_get_uint8(v___y_2163_, sizeof(void*)*3 + 2);
v_checkDeprecated_2171_ = lean_ctor_get_uint8(v___y_2163_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2172_ = lean_ctor_get_uint8(v___y_2163_, sizeof(void*)*3 + 4);
v_ref_2173_ = l_Lean_replaceRef(v_ref_2157_, v_ref_2168_);
lean_inc(v_currRecDepth_2167_);
lean_inc_ref(v_toCold_2166_);
v___x_2174_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2174_, 0, v_toCold_2166_);
lean_ctor_set(v___x_2174_, 1, v_currRecDepth_2167_);
lean_ctor_set(v___x_2174_, 2, v_ref_2173_);
lean_ctor_set_uint16(v___x_2174_, sizeof(void*)*3, v_optionFlags_2169_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*3 + 2, v_suppressElabErrors_2170_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*3 + 3, v_checkDeprecated_2171_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*3 + 4, v_isRecordingDeps_2172_);
v___x_2175_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___x_2174_, v___y_2164_);
lean_dec_ref_known(v___x_2174_, 3);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2176_, lean_object* v_msg_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2176_, v_msg_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_ref_2176_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2186_, lean_object* v_currNamespace_2187_, lean_object* v_openDecls_2188_, lean_object* v_n_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = l_Lean_ResolveName_resolveNamespace(v_env_2186_, v_currNamespace_2187_, v_openDecls_2188_, v_n_2189_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___y_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2194_, lean_object* v_currNamespace_2195_, lean_object* v_openDecls_2196_, lean_object* v_n_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2194_, v_currNamespace_2195_, v_openDecls_2196_, v_n_2197_, v___y_2198_, v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0(lean_object* v___x_2201_, lean_object* v_entry_2202_, lean_object* v_s_2203_){
_start:
{
lean_object* v_addEntryFn_2204_; lean_object* v_importedEntries_2205_; lean_object* v_state_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_addEntryFn_2204_ = lean_ctor_get(v___x_2201_, 3);
lean_inc(v_addEntryFn_2204_);
lean_dec_ref(v___x_2201_);
v_importedEntries_2205_ = lean_ctor_get(v_s_2203_, 0);
v_state_2206_ = lean_ctor_get(v_s_2203_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_s_2203_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v_s_2203_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_state_2206_);
lean_inc(v_importedEntries_2205_);
lean_dec(v_s_2203_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_state_2210_; lean_object* v___x_2212_; 
v_state_2210_ = lean_apply_2(v_addEntryFn_2204_, v_state_2206_, v_entry_2202_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v_state_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_importedEntries_2205_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_state_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(lean_object* v_keys_2215_, lean_object* v_i_2216_, lean_object* v_k_2217_){
_start:
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_array_get_size(v_keys_2215_);
v___x_2219_ = lean_nat_dec_lt(v_i_2216_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_dec(v_i_2216_);
return v___x_2219_;
}
else
{
lean_object* v_k_x27_2220_; uint8_t v___x_2221_; 
v_k_x27_2220_ = lean_array_fget_borrowed(v_keys_2215_, v_i_2216_);
v___x_2221_ = l_Lean_instBEqExtraModUse_beq(v_k_2217_, v_k_x27_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_unsigned_to_nat(1u);
v___x_2223_ = lean_nat_add(v_i_2216_, v___x_2222_);
lean_dec(v_i_2216_);
v_i_2216_ = v___x_2223_;
goto _start;
}
else
{
lean_dec(v_i_2216_);
return v___x_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg___boxed(lean_object* v_keys_2225_, lean_object* v_i_2226_, lean_object* v_k_2227_){
_start:
{
uint8_t v_res_2228_; lean_object* v_r_2229_; 
v_res_2228_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(v_keys_2225_, v_i_2226_, v_k_2227_);
lean_dec_ref(v_k_2227_);
lean_dec_ref(v_keys_2225_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(lean_object* v_x_2230_, size_t v_x_2231_, lean_object* v_x_2232_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 0)
{
lean_object* v_es_2233_; lean_object* v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v_j_2237_; lean_object* v___x_2238_; 
v_es_2233_ = lean_ctor_get(v_x_2230_, 0);
v___x_2234_ = lean_box(2);
v___x_2235_ = ((size_t)31ULL);
v___x_2236_ = lean_usize_land(v_x_2231_, v___x_2235_);
v_j_2237_ = lean_usize_to_nat(v___x_2236_);
v___x_2238_ = lean_array_get_borrowed(v___x_2234_, v_es_2233_, v_j_2237_);
lean_dec(v_j_2237_);
switch(lean_obj_tag(v___x_2238_))
{
case 0:
{
lean_object* v_key_2239_; uint8_t v___x_2240_; 
v_key_2239_ = lean_ctor_get(v___x_2238_, 0);
v___x_2240_ = l_Lean_instBEqExtraModUse_beq(v_x_2232_, v_key_2239_);
return v___x_2240_;
}
case 1:
{
lean_object* v_node_2241_; size_t v___x_2242_; size_t v___x_2243_; 
v_node_2241_ = lean_ctor_get(v___x_2238_, 0);
v___x_2242_ = ((size_t)5ULL);
v___x_2243_ = lean_usize_shift_right(v_x_2231_, v___x_2242_);
v_x_2230_ = v_node_2241_;
v_x_2231_ = v___x_2243_;
goto _start;
}
default: 
{
uint8_t v___x_2245_; 
v___x_2245_ = 0;
return v___x_2245_;
}
}
}
else
{
lean_object* v_ks_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_ks_2246_ = lean_ctor_get(v_x_2230_, 0);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(v_ks_2246_, v___x_2247_, v_x_2232_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg___boxed(lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
size_t v_x_29954__boxed_2252_; uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_x_29954__boxed_2252_ = lean_unbox_usize(v_x_2250_);
lean_dec(v_x_2250_);
v_res_2253_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(v_x_2249_, v_x_29954__boxed_2252_, v_x_2251_);
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_x_2249_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(lean_object* v_x_2255_, lean_object* v_x_2256_){
_start:
{
uint64_t v___x_2257_; size_t v___x_2258_; uint8_t v___x_2259_; 
v___x_2257_ = l_Lean_instHashableExtraModUse_hash(v_x_2256_);
v___x_2258_ = lean_uint64_to_usize(v___x_2257_);
v___x_2259_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(v_x_2255_, v___x_2258_, v_x_2256_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg___boxed(lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
uint8_t v_res_2262_; lean_object* v_r_2263_; 
v_res_2262_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(v_x_2260_, v_x_2261_);
lean_dec_ref(v_x_2261_);
lean_dec_ref(v_x_2260_);
v_r_2263_ = lean_box(v_res_2262_);
return v_r_2263_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v_cls_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_cls_2276_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2277_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2278_ = l_Lean_Name_append(v___x_2277_, v_cls_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9));
v___x_2281_ = l_Lean_stringToMessageData(v___x_2280_);
return v___x_2281_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2284_ = l_Lean_stringToMessageData(v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2289_, uint8_t v_isMeta_2290_, lean_object* v_hint_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_env_2333_; uint8_t v_isExporting_2334_; lean_object* v_entry_2335_; lean_object* v___x_2336_; lean_object* v_env_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0);
v___x_2332_ = lean_st_ref_get(v___y_2297_);
v_env_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_ref(v_env_2333_);
lean_dec(v___x_2332_);
v_isExporting_2334_ = lean_ctor_get_uint8(v_env_2333_, sizeof(void*)*13);
lean_dec_ref(v_env_2333_);
lean_inc(v_mod_2289_);
v_entry_2335_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2335_, 0, v_mod_2289_);
lean_ctor_set_uint8(v_entry_2335_, sizeof(void*)*1, v_isExporting_2334_);
lean_ctor_set_uint8(v_entry_2335_, sizeof(void*)*1 + 1, v_isMeta_2290_);
v___x_2336_ = lean_st_ref_get(v___y_2297_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_ref(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2338_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2339_ = lean_box(1);
v___x_2340_ = lean_box(0);
v___x_2341_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2331_, v___x_2338_, v_env_2337_, v___x_2339_, v___x_2340_);
v___x_2342_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(v___x_2341_, v_entry_2335_);
lean_dec(v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v_toCold_2343_; lean_object* v_options_2344_; lean_object* v_inheritedTraceOptions_2345_; uint8_t v_hasTrace_2346_; lean_object* v___f_2347_; uint8_t v___x_2348_; lean_object* v___y_2350_; lean_object* v___y_2351_; 
v_toCold_2343_ = lean_ctor_get(v___y_2296_, 0);
v_options_2344_ = lean_ctor_get(v_toCold_2343_, 2);
v_inheritedTraceOptions_2345_ = lean_ctor_get(v_toCold_2343_, 11);
v_hasTrace_2346_ = lean_ctor_get_uint8(v_options_2344_, sizeof(void*)*1);
v___f_2347_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_2347_, 0, v___x_2338_);
lean_closure_set(v___f_2347_, 1, v_entry_2335_);
v___x_2348_ = 1;
if (v_hasTrace_2346_ == 0)
{
lean_dec(v_hint_2291_);
lean_dec(v_mod_2289_);
v___y_2350_ = v___y_2295_;
v___y_2351_ = v___y_2297_;
goto v___jp_2349_;
}
else
{
lean_object* v_cls_2378_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_cls_2378_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2));
v___x_2398_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2345_, v_options_2344_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec(v_hint_2291_);
lean_dec(v_mod_2289_);
v___y_2350_ = v___y_2295_;
v___y_2351_ = v___y_2297_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2400_; lean_object* v___y_2402_; 
v___x_2400_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
if (v_isExporting_2334_ == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2402_ = v___x_2409_;
goto v___jp_2401_;
}
else
{
lean_object* v___x_2410_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2402_ = v___x_2410_;
goto v___jp_2401_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_inc_ref(v___y_2402_);
v___x_2403_ = l_Lean_stringToMessageData(v___y_2402_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2400_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
if (v_isMeta_2290_ == 0)
{
lean_object* v___x_2407_; 
v___x_2407_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___y_2385_ = v___x_2406_;
v___y_2386_ = v___x_2407_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14));
v___y_2385_ = v___x_2406_;
v___y_2386_ = v___x_2408_;
goto v___jp_2384_;
}
}
}
v___jp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___y_2380_);
lean_ctor_set(v___x_2382_, 1, v___y_2381_);
v___x_2383_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2378_, v___x_2382_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_dec_ref_known(v___x_2383_, 1);
v___y_2350_ = v___y_2295_;
v___y_2351_ = v___y_2297_;
goto v___jp_2349_;
}
else
{
lean_dec_ref(v___f_2347_);
return v___x_2383_;
}
}
v___jp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
lean_inc_ref(v___y_2386_);
v___x_2387_ = l_Lean_stringToMessageData(v___y_2386_);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___y_2385_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = l_Lean_MessageData_ofName(v_mod_2289_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = l_Lean_Name_isAnonymous(v_hint_2291_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2395_ = l_Lean_MessageData_ofName(v_hint_2291_);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___y_2380_ = v___x_2392_;
v___y_2381_ = v___x_2396_;
goto v___jp_2379_;
}
else
{
lean_object* v___x_2397_; 
lean_dec(v_hint_2291_);
v___x_2397_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7);
v___y_2380_ = v___x_2392_;
v___y_2381_ = v___x_2397_;
goto v___jp_2379_;
}
}
}
v___jp_2349_:
{
lean_object* v___x_2352_; lean_object* v_toEnvExtension_2353_; uint8_t v_logWrites_2354_; 
v___x_2352_ = lean_st_ref_take(v___y_2351_);
v_toEnvExtension_2353_ = lean_ctor_get(v___x_2338_, 0);
v_logWrites_2354_ = lean_ctor_get_uint8(v_toEnvExtension_2353_, sizeof(void*)*6);
if (v_logWrites_2354_ == 0)
{
lean_object* v_env_2355_; lean_object* v_nextMacroScope_2356_; lean_object* v_ngen_2357_; lean_object* v_auxDeclNGen_2358_; lean_object* v_traceState_2359_; lean_object* v_recordedDeps_2360_; lean_object* v_messages_2361_; lean_object* v_infoState_2362_; lean_object* v_snapshotTasks_2363_; lean_object* v_asyncMode_2364_; lean_object* v___x_2365_; 
v_env_2355_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_env_2355_);
v_nextMacroScope_2356_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_nextMacroScope_2356_);
v_ngen_2357_ = lean_ctor_get(v___x_2352_, 2);
lean_inc_ref(v_ngen_2357_);
v_auxDeclNGen_2358_ = lean_ctor_get(v___x_2352_, 3);
lean_inc_ref(v_auxDeclNGen_2358_);
v_traceState_2359_ = lean_ctor_get(v___x_2352_, 4);
lean_inc_ref(v_traceState_2359_);
v_recordedDeps_2360_ = lean_ctor_get(v___x_2352_, 6);
lean_inc_ref(v_recordedDeps_2360_);
v_messages_2361_ = lean_ctor_get(v___x_2352_, 7);
lean_inc_ref(v_messages_2361_);
v_infoState_2362_ = lean_ctor_get(v___x_2352_, 8);
lean_inc_ref(v_infoState_2362_);
v_snapshotTasks_2363_ = lean_ctor_get(v___x_2352_, 9);
lean_inc_ref(v_snapshotTasks_2363_);
lean_dec(v___x_2352_);
v_asyncMode_2364_ = lean_ctor_get(v_toEnvExtension_2353_, 2);
lean_inc_ref(v_toEnvExtension_2353_);
v___x_2365_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2353_, v_env_2355_, v___f_2347_, v_asyncMode_2364_, v___x_2340_, v___x_2348_);
v___y_2300_ = v___y_2351_;
v___y_2301_ = v___y_2350_;
v___y_2302_ = v_recordedDeps_2360_;
v___y_2303_ = v_auxDeclNGen_2358_;
v___y_2304_ = v_messages_2361_;
v___y_2305_ = v_ngen_2357_;
v___y_2306_ = v_nextMacroScope_2356_;
v___y_2307_ = v_traceState_2359_;
v___y_2308_ = v_infoState_2362_;
v___y_2309_ = v_snapshotTasks_2363_;
v___y_2310_ = v___x_2365_;
goto v___jp_2299_;
}
else
{
lean_object* v_env_2366_; lean_object* v_nextMacroScope_2367_; lean_object* v_ngen_2368_; lean_object* v_auxDeclNGen_2369_; lean_object* v_traceState_2370_; lean_object* v_recordedDeps_2371_; lean_object* v_messages_2372_; lean_object* v_infoState_2373_; lean_object* v_snapshotTasks_2374_; lean_object* v_asyncMode_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_env_2366_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_env_2366_);
v_nextMacroScope_2367_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_nextMacroScope_2367_);
v_ngen_2368_ = lean_ctor_get(v___x_2352_, 2);
lean_inc_ref(v_ngen_2368_);
v_auxDeclNGen_2369_ = lean_ctor_get(v___x_2352_, 3);
lean_inc_ref(v_auxDeclNGen_2369_);
v_traceState_2370_ = lean_ctor_get(v___x_2352_, 4);
lean_inc_ref(v_traceState_2370_);
v_recordedDeps_2371_ = lean_ctor_get(v___x_2352_, 6);
lean_inc_ref(v_recordedDeps_2371_);
v_messages_2372_ = lean_ctor_get(v___x_2352_, 7);
lean_inc_ref(v_messages_2372_);
v_infoState_2373_ = lean_ctor_get(v___x_2352_, 8);
lean_inc_ref(v_infoState_2373_);
v_snapshotTasks_2374_ = lean_ctor_get(v___x_2352_, 9);
lean_inc_ref(v_snapshotTasks_2374_);
lean_dec(v___x_2352_);
v_asyncMode_2375_ = lean_ctor_get(v_toEnvExtension_2353_, 2);
lean_inc_ref_n(v_toEnvExtension_2353_, 2);
v___x_2376_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2353_, v_env_2366_);
lean_dec_ref(v_env_2366_);
v___x_2377_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2353_, v___x_2376_, v___f_2347_, v_asyncMode_2375_, v___x_2340_, v___x_2348_);
v___y_2300_ = v___y_2351_;
v___y_2301_ = v___y_2350_;
v___y_2302_ = v_recordedDeps_2371_;
v___y_2303_ = v_auxDeclNGen_2369_;
v___y_2304_ = v_messages_2372_;
v___y_2305_ = v_ngen_2368_;
v___y_2306_ = v_nextMacroScope_2367_;
v___y_2307_ = v_traceState_2370_;
v___y_2308_ = v_infoState_2373_;
v___y_2309_ = v_snapshotTasks_2374_;
v___y_2310_ = v___x_2377_;
goto v___jp_2299_;
}
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref_known(v_entry_2335_, 1);
lean_dec(v_hint_2291_);
lean_dec(v_mod_2289_);
v___x_2411_ = lean_box(0);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
v___jp_2299_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_mctx_2315_; lean_object* v_zetaDeltaFVarIds_2316_; lean_object* v_postponed_2317_; lean_object* v_diag_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2329_; 
v___x_2311_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_2312_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2312_, 0, v___y_2310_);
lean_ctor_set(v___x_2312_, 1, v___y_2306_);
lean_ctor_set(v___x_2312_, 2, v___y_2305_);
lean_ctor_set(v___x_2312_, 3, v___y_2303_);
lean_ctor_set(v___x_2312_, 4, v___y_2307_);
lean_ctor_set(v___x_2312_, 5, v___x_2311_);
lean_ctor_set(v___x_2312_, 6, v___y_2302_);
lean_ctor_set(v___x_2312_, 7, v___y_2304_);
lean_ctor_set(v___x_2312_, 8, v___y_2308_);
lean_ctor_set(v___x_2312_, 9, v___y_2309_);
v___x_2313_ = lean_st_ref_put(v___y_2300_, v___x_2312_);
v___x_2314_ = lean_st_ref_take(v___y_2301_);
v_mctx_2315_ = lean_ctor_get(v___x_2314_, 0);
v_zetaDeltaFVarIds_2316_ = lean_ctor_get(v___x_2314_, 2);
v_postponed_2317_ = lean_ctor_get(v___x_2314_, 3);
v_diag_2318_ = lean_ctor_get(v___x_2314_, 4);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2314_, 1);
lean_dec(v_unused_2330_);
v___x_2320_ = v___x_2314_;
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_diag_2318_);
lean_inc(v_postponed_2317_);
lean_inc(v_zetaDeltaFVarIds_2316_);
lean_inc(v_mctx_2315_);
lean_dec(v___x_2314_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_mctx_2315_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_zetaDeltaFVarIds_2316_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_postponed_2317_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_diag_2318_);
v___x_2325_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_st_ref_put(v___y_2301_, v___x_2325_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2322_);
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2413_, lean_object* v_isMeta_2414_, lean_object* v_hint_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v_isMeta_boxed_2423_; lean_object* v_res_2424_; 
v_isMeta_boxed_2423_ = lean_unbox(v_isMeta_2414_);
v_res_2424_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2413_, v_isMeta_boxed_2423_, v_hint_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2425_, lean_object* v_declName_2426_, lean_object* v_as_2427_, size_t v_sz_2428_, size_t v_i_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_lt(v_i_2429_, v_sz_2428_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_dec(v_declName_2426_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v_b_2430_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; lean_object* v_modules_2441_; lean_object* v___x_2442_; lean_object* v_a_2443_; lean_object* v___x_2444_; lean_object* v_toImport_2445_; lean_object* v_module_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2440_ = l_Lean_Environment_header(v___x_2425_);
v_modules_2441_ = lean_ctor_get(v___x_2440_, 3);
lean_inc_ref(v_modules_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2443_ = lean_array_uget_borrowed(v_as_2427_, v_i_2429_);
v___x_2444_ = lean_array_get(v___x_2442_, v_modules_2441_, v_a_2443_);
lean_dec_ref(v_modules_2441_);
v_toImport_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc_ref(v_toImport_2445_);
lean_dec(v___x_2444_);
v_module_2446_ = lean_ctor_get(v_toImport_2445_, 0);
lean_inc(v_module_2446_);
lean_dec_ref(v_toImport_2445_);
v___x_2447_ = lean_box(0);
v___x_2448_ = 0;
lean_inc(v_declName_2426_);
v___x_2449_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2446_, v___x_2448_, v_declName_2426_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2449_) == 0)
{
size_t v___x_2450_; size_t v___x_2451_; 
lean_dec_ref_known(v___x_2449_, 1);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2429_, v___x_2450_);
v_i_2429_ = v___x_2451_;
v_b_2430_ = v___x_2447_;
goto _start;
}
else
{
lean_dec(v_declName_2426_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2453_, lean_object* v_declName_2454_, lean_object* v_as_2455_, lean_object* v_sz_2456_, lean_object* v_i_2457_, lean_object* v_b_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
size_t v_sz_boxed_2466_; size_t v_i_boxed_2467_; lean_object* v_res_2468_; 
v_sz_boxed_2466_ = lean_unbox_usize(v_sz_2456_);
lean_dec(v_sz_2456_);
v_i_boxed_2467_ = lean_unbox_usize(v_i_2457_);
lean_dec(v_i_2457_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2453_, v_declName_2454_, v_as_2455_, v_sz_boxed_2466_, v_i_boxed_2467_, v_b_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v_as_2455_);
lean_dec_ref(v___x_2453_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(lean_object* v_a_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2470_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_box(0);
return v___x_2471_;
}
else
{
lean_object* v_key_2472_; lean_object* v_value_2473_; lean_object* v_tail_2474_; uint8_t v___x_2475_; 
v_key_2472_ = lean_ctor_get(v_x_2470_, 0);
v_value_2473_ = lean_ctor_get(v_x_2470_, 1);
v_tail_2474_ = lean_ctor_get(v_x_2470_, 2);
v___x_2475_ = lean_name_eq(v_key_2472_, v_a_2469_);
if (v___x_2475_ == 0)
{
v_x_2470_ = v_tail_2474_;
goto _start;
}
else
{
lean_object* v___x_2477_; 
lean_inc(v_value_2473_);
v___x_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_value_2473_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg___boxed(lean_object* v_a_2478_, lean_object* v_x_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(v_a_2478_, v_x_2479_);
lean_dec(v_x_2479_);
lean_dec(v_a_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_buckets_2483_; lean_object* v___x_2484_; uint64_t v___y_2486_; 
v_buckets_2483_ = lean_ctor_get(v_m_2481_, 1);
v___x_2484_ = lean_array_get_size(v_buckets_2483_);
if (lean_obj_tag(v_a_2482_) == 0)
{
uint64_t v___x_2500_; 
v___x_2500_ = 1723ULL;
v___y_2486_ = v___x_2500_;
goto v___jp_2485_;
}
else
{
uint64_t v_hash_2501_; 
v_hash_2501_ = lean_ctor_get_uint64(v_a_2482_, sizeof(void*)*2);
v___y_2486_ = v_hash_2501_;
goto v___jp_2485_;
}
v___jp_2485_:
{
uint64_t v___x_2487_; uint64_t v___x_2488_; uint64_t v_fold_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; uint64_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2487_ = 32ULL;
v___x_2488_ = lean_uint64_shift_right(v___y_2486_, v___x_2487_);
v_fold_2489_ = lean_uint64_xor(v___y_2486_, v___x_2488_);
v___x_2490_ = 16ULL;
v___x_2491_ = lean_uint64_shift_right(v_fold_2489_, v___x_2490_);
v___x_2492_ = lean_uint64_xor(v_fold_2489_, v___x_2491_);
v___x_2493_ = lean_uint64_to_usize(v___x_2492_);
v___x_2494_ = lean_usize_of_nat(v___x_2484_);
v___x_2495_ = ((size_t)1ULL);
v___x_2496_ = lean_usize_sub(v___x_2494_, v___x_2495_);
v___x_2497_ = lean_usize_land(v___x_2493_, v___x_2496_);
v___x_2498_ = lean_array_uget_borrowed(v_buckets_2483_, v___x_2497_);
v___x_2499_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(v_a_2482_, v___x_2498_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_m_2502_);
return v_res_2504_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2508_, uint8_t v_isMeta_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_env_2522_; lean_object* v___y_2524_; lean_object* v___x_2537_; 
v___x_2517_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0);
v___x_2518_ = lean_st_ref_get(v___y_2515_);
v_env_2522_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_env_2522_);
lean_dec(v___x_2518_);
v___x_2537_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2522_, v_declName_2508_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref(v_env_2522_);
lean_dec(v_declName_2508_);
goto v___jp_2519_;
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2539_; lean_object* v_modules_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_val_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___x_2539_ = l_Lean_Environment_header(v_env_2522_);
v_modules_2540_ = lean_ctor_get(v___x_2539_, 3);
lean_inc_ref(v_modules_2540_);
lean_dec_ref(v___x_2539_);
v___x_2541_ = lean_array_get_size(v_modules_2540_);
v___x_2542_ = lean_nat_dec_lt(v_val_2538_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v_modules_2540_);
lean_dec(v_val_2538_);
lean_dec_ref(v_env_2522_);
lean_dec(v_declName_2508_);
goto v___jp_2519_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___y_2546_; 
v___x_2543_ = lean_array_fget(v_modules_2540_, v_val_2538_);
lean_dec(v_val_2538_);
lean_dec_ref(v_modules_2540_);
v___x_2544_ = lean_st_ref_get(v___y_2515_);
if (v_isMeta_2509_ == 0)
{
lean_dec(v___x_2544_);
v___y_2546_ = v_isMeta_2509_;
goto v___jp_2545_;
}
else
{
lean_object* v_env_2557_; uint8_t v___x_2558_; 
v_env_2557_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_env_2557_);
lean_dec(v___x_2544_);
lean_inc(v_declName_2508_);
v___x_2558_ = l_Lean_isMarkedMeta(v_env_2557_, v_declName_2508_);
if (v___x_2558_ == 0)
{
v___y_2546_ = v_isMeta_2509_;
goto v___jp_2545_;
}
else
{
uint8_t v___x_2559_; 
v___x_2559_ = 0;
v___y_2546_ = v___x_2559_;
goto v___jp_2545_;
}
}
v___jp_2545_:
{
lean_object* v_toImport_2547_; lean_object* v_module_2548_; lean_object* v___x_2549_; 
v_toImport_2547_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_toImport_2547_);
lean_dec(v___x_2543_);
v_module_2548_ = lean_ctor_get(v_toImport_2547_, 0);
lean_inc(v_module_2548_);
lean_dec_ref(v_toImport_2547_);
lean_inc(v_declName_2508_);
v___x_2549_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2548_, v___y_2546_, v_declName_2508_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec_ref_known(v___x_2549_, 1);
v___x_2550_ = l_Lean_indirectModUseExt;
v___x_2551_ = lean_box(1);
v___x_2552_ = lean_box(0);
lean_inc_ref(v_env_2522_);
v___x_2553_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2517_, v___x_2550_, v_env_2522_, v___x_2551_, v___x_2552_);
v___x_2554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2553_, v_declName_2508_);
lean_dec(v___x_2553_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___y_2524_ = v___x_2555_;
goto v___jp_2523_;
}
else
{
lean_object* v_val_2556_; 
v_val_2556_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v___x_2554_, 1);
v___y_2524_ = v_val_2556_;
goto v___jp_2523_;
}
}
else
{
lean_dec_ref(v_env_2522_);
lean_dec(v_declName_2508_);
return v___x_2549_;
}
}
}
}
v___jp_2519_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
v___jp_2523_:
{
lean_object* v___x_2525_; size_t v_sz_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2525_ = lean_box(0);
v_sz_2526_ = lean_array_size(v___y_2524_);
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2522_, v_declName_2508_, v___y_2524_, v_sz_2526_, v___x_2527_, v___x_2525_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_env_2522_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2528_, 0);
lean_dec(v_unused_2536_);
v___x_2530_ = v___x_2528_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_dec(v___x_2528_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2525_);
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2525_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
return v___x_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2560_, lean_object* v_isMeta_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
uint8_t v_isMeta_boxed_2569_; lean_object* v_res_2570_; 
v_isMeta_boxed_2569_ = lean_unbox(v_isMeta_2561_);
v_res_2570_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2560_, v_isMeta_boxed_2569_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2571_, lean_object* v_b_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
if (lean_obj_tag(v_as_x27_2571_) == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_b_2572_);
return v___x_2580_;
}
else
{
lean_object* v_head_2581_; lean_object* v_tail_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
v_head_2581_ = lean_ctor_get(v_as_x27_2571_, 0);
v_tail_2582_ = lean_ctor_get(v_as_x27_2571_, 1);
v___x_2583_ = lean_box(0);
v___x_2584_ = 1;
lean_inc(v_head_2581_);
v___x_2585_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2581_, v___x_2584_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
v_as_x27_2571_ = v_tail_2582_;
v_b_2572_ = v___x_2583_;
goto _start;
}
else
{
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2587_, lean_object* v_b_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2587_, v_b_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v_as_x27_2587_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_env_2597_, lean_object* v___x_2598_, lean_object* v_currNamespace_2599_, lean_object* v_openDecls_2600_, lean_object* v_n_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = l_Lean_ResolveName_resolveGlobalName(v_env_2597_, v___x_2598_, v_currNamespace_2599_, v_openDecls_2600_, v_n_2601_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_env_2606_, lean_object* v___x_2607_, lean_object* v_currNamespace_2608_, lean_object* v_openDecls_2609_, lean_object* v_n_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_env_2606_, v___x_2607_, v_currNamespace_2608_, v_openDecls_2609_, v_n_2610_, v___y_2611_, v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v___x_2607_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2614_, lean_object* v_declName_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v___x_2618_; lean_object* v_env_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; uint8_t v___x_2622_; 
v___x_2618_ = 0;
v_env_2619_ = l_Lean_Environment_setExporting(v_env_2614_, v___x_2618_);
lean_inc(v_declName_2615_);
v___x_2620_ = l_Lean_mkPrivateName(v_env_2619_, v_declName_2615_);
v___x_2621_ = 1;
lean_inc_ref(v_env_2619_);
v___x_2622_ = l_Lean_Environment_contains(v_env_2619_, v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2623_ = l_Lean_privateToUserName(v_declName_2615_);
v___x_2624_ = l_Lean_Environment_contains(v_env_2619_, v___x_2623_, v___x_2621_);
v___x_2625_ = lean_box(v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v___y_2617_);
return v___x_2626_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v_env_2619_);
lean_dec(v_declName_2615_);
v___x_2627_ = lean_box(v___x_2622_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___y_2617_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2629_, lean_object* v_declName_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2629_, v_declName_2630_, v___y_2631_, v___y_2632_);
lean_dec_ref(v___y_2631_);
return v_res_2633_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = l_Lean_maxRecDepthErrorMessage;
v___x_2640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2642_ = l_Lean_MessageData_ofFormat(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2644_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2645_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v___x_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2648_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2649_, 0, v_ref_2646_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v_toCold_2664_; lean_object* v_env_2665_; lean_object* v_currRecDepth_2666_; lean_object* v_ref_2667_; lean_object* v_maxRecDepth_2668_; lean_object* v_currNamespace_2669_; lean_object* v_openDecls_2670_; lean_object* v_quotContext_2671_; lean_object* v_currMacroScope_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___x_2675_; lean_object* v___f_2676_; lean_object* v___f_2677_; lean_object* v___f_2678_; lean_object* v_methods_2679_; lean_object* v___x_2680_; lean_object* v_nextMacroScope_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2663_ = lean_st_ref_get(v___y_2661_);
v_toCold_2664_ = lean_ctor_get(v___y_2660_, 0);
v_env_2665_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref_n(v_env_2665_, 4);
lean_dec(v___x_2663_);
v_currRecDepth_2666_ = lean_ctor_get(v___y_2660_, 1);
v_ref_2667_ = lean_ctor_get(v___y_2660_, 2);
v_maxRecDepth_2668_ = lean_ctor_get(v_toCold_2664_, 3);
v_currNamespace_2669_ = lean_ctor_get(v_toCold_2664_, 4);
v_openDecls_2670_ = lean_ctor_get(v_toCold_2664_, 5);
v_quotContext_2671_ = lean_ctor_get(v_toCold_2664_, 8);
v_currMacroScope_2672_ = lean_ctor_get(v_toCold_2664_, 9);
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2673_, 0, v_env_2665_);
v___f_2674_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2674_, 0, v_env_2665_);
v___x_2675_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2660_);
lean_inc_n(v_currNamespace_2669_, 3);
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2676_, 0, v_currNamespace_2669_);
lean_inc_n(v_openDecls_2670_, 2);
v___f_2677_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2677_, 0, v_env_2665_);
lean_closure_set(v___f_2677_, 1, v___x_2675_);
lean_closure_set(v___f_2677_, 2, v_currNamespace_2669_);
lean_closure_set(v___f_2677_, 3, v_openDecls_2670_);
v___f_2678_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2678_, 0, v_env_2665_);
lean_closure_set(v___f_2678_, 1, v_currNamespace_2669_);
lean_closure_set(v___f_2678_, 2, v_openDecls_2670_);
v_methods_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2679_, 0, v___f_2674_);
lean_ctor_set(v_methods_2679_, 1, v___f_2676_);
lean_ctor_set(v_methods_2679_, 2, v___f_2673_);
lean_ctor_set(v_methods_2679_, 3, v___f_2678_);
lean_ctor_set(v_methods_2679_, 4, v___f_2677_);
v___x_2680_ = lean_st_ref_get(v___y_2661_);
v_nextMacroScope_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc(v_nextMacroScope_2681_);
lean_dec(v___x_2680_);
lean_inc(v_ref_2667_);
lean_inc(v_maxRecDepth_2668_);
lean_inc(v_currRecDepth_2666_);
lean_inc(v_currMacroScope_2672_);
lean_inc(v_quotContext_2671_);
v___x_2682_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2682_, 0, v_methods_2679_);
lean_ctor_set(v___x_2682_, 1, v_quotContext_2671_);
lean_ctor_set(v___x_2682_, 2, v_currMacroScope_2672_);
lean_ctor_set(v___x_2682_, 3, v_currRecDepth_2666_);
lean_ctor_set(v___x_2682_, 4, v_maxRecDepth_2668_);
lean_ctor_set(v___x_2682_, 5, v_ref_2667_);
v___x_2683_ = lean_box(0);
v___x_2684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2684_, 0, v_nextMacroScope_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
v___x_2685_ = lean_apply_2(v_x_2655_, v___x_2682_, v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v_a_2687_; lean_object* v_macroScope_2688_; lean_object* v_traceMsgs_2689_; lean_object* v_expandedMacroDecls_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 1);
lean_inc(v_a_2686_);
v_a_2687_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2685_, 2);
v_macroScope_2688_ = lean_ctor_get(v_a_2686_, 0);
lean_inc(v_macroScope_2688_);
v_traceMsgs_2689_ = lean_ctor_get(v_a_2686_, 1);
lean_inc(v_traceMsgs_2689_);
v_expandedMacroDecls_2690_ = lean_ctor_get(v_a_2686_, 2);
lean_inc(v_expandedMacroDecls_2690_);
lean_dec(v_a_2686_);
v___x_2691_ = lean_box(0);
v___x_2692_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2690_, v___x_2691_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v_expandedMacroDecls_2690_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2693_; lean_object* v_env_2694_; lean_object* v_ngen_2695_; lean_object* v_auxDeclNGen_2696_; lean_object* v_traceState_2697_; lean_object* v_cache_2698_; lean_object* v_recordedDeps_2699_; lean_object* v_messages_2700_; lean_object* v_infoState_2701_; lean_object* v_snapshotTasks_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref_known(v___x_2692_, 1);
v___x_2693_ = lean_st_ref_take(v___y_2661_);
v_env_2694_ = lean_ctor_get(v___x_2693_, 0);
v_ngen_2695_ = lean_ctor_get(v___x_2693_, 2);
v_auxDeclNGen_2696_ = lean_ctor_get(v___x_2693_, 3);
v_traceState_2697_ = lean_ctor_get(v___x_2693_, 4);
v_cache_2698_ = lean_ctor_get(v___x_2693_, 5);
v_recordedDeps_2699_ = lean_ctor_get(v___x_2693_, 6);
v_messages_2700_ = lean_ctor_get(v___x_2693_, 7);
v_infoState_2701_ = lean_ctor_get(v___x_2693_, 8);
v_snapshotTasks_2702_ = lean_ctor_get(v___x_2693_, 9);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2693_, 1);
lean_dec(v_unused_2729_);
v___x_2704_ = v___x_2693_;
v_isShared_2705_ = v_isSharedCheck_2728_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_snapshotTasks_2702_);
lean_inc(v_infoState_2701_);
lean_inc(v_messages_2700_);
lean_inc(v_recordedDeps_2699_);
lean_inc(v_cache_2698_);
lean_inc(v_traceState_2697_);
lean_inc(v_auxDeclNGen_2696_);
lean_inc(v_ngen_2695_);
lean_inc(v_env_2694_);
lean_dec(v___x_2693_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2728_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v_macroScope_2688_);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_env_2694_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_macroScope_2688_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_ngen_2695_);
lean_ctor_set(v_reuseFailAlloc_2727_, 3, v_auxDeclNGen_2696_);
lean_ctor_set(v_reuseFailAlloc_2727_, 4, v_traceState_2697_);
lean_ctor_set(v_reuseFailAlloc_2727_, 5, v_cache_2698_);
lean_ctor_set(v_reuseFailAlloc_2727_, 6, v_recordedDeps_2699_);
lean_ctor_set(v_reuseFailAlloc_2727_, 7, v_messages_2700_);
lean_ctor_set(v_reuseFailAlloc_2727_, 8, v_infoState_2701_);
lean_ctor_set(v_reuseFailAlloc_2727_, 9, v_snapshotTasks_2702_);
v___x_2707_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_st_ref_put(v___y_2661_, v___x_2707_);
v___x_2709_ = l_List_reverse___redArg(v_traceMsgs_2689_);
v___x_2710_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2709_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; 
v_unused_2718_ = lean_ctor_get(v___x_2710_, 0);
lean_dec(v_unused_2718_);
v___x_2712_ = v___x_2710_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_dec(v___x_2710_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_a_2687_);
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2687_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2687_);
v_a_2719_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2710_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2710_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_traceMsgs_2689_);
lean_dec(v_macroScope_2688_);
lean_dec(v_a_2687_);
v_a_2730_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2692_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2692_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; 
v_a_2738_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2685_, 2);
if (lean_obj_tag(v_a_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v_a_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_a_2739_ = lean_ctor_get(v_a_2738_, 0);
lean_inc(v_a_2739_);
v_a_2740_ = lean_ctor_get(v_a_2738_, 1);
lean_inc_ref(v_a_2740_);
lean_dec_ref_known(v_a_2738_, 2);
v___x_2741_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2742_ = lean_string_dec_eq(v_a_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_a_2740_);
v___x_2744_ = l_Lean_MessageData_ofFormat(v___x_2743_);
v___x_2745_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2739_, v___x_2744_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v_a_2739_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; 
lean_dec_ref(v_a_2740_);
v___x_2746_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2739_);
return v___x_2746_;
}
}
else
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2756_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = lean_box(0);
v___x_2761_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2762_ = l_Lean_mkConst(v___x_2761_, v___x_2760_);
return v___x_2762_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2773_ = l_Lean_mkConst(v___x_2772_, v___x_2771_);
return v___x_2773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2776_, lean_object* v_as_2777_, size_t v_sz_2778_, size_t v_i_2779_, lean_object* v_b_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_a_2789_; uint8_t v___x_2793_; 
v___x_2793_ = lean_usize_dec_lt(v_i_2779_, v_sz_2778_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_b_2780_);
return v___x_2794_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_a_2797_; uint8_t v___x_2798_; 
v___x_2795_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2796_ = lean_box(0);
v_a_2797_ = lean_array_uget_borrowed(v_as_2777_, v_i_2779_);
lean_inc(v_a_2797_);
v___x_2798_ = l_Lean_Syntax_isOfKind(v_a_2797_, v___x_2795_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_dec_ref_known(v___x_2799_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2799_;
}
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = l_Lean_Syntax_getArg(v_a_2797_, v___x_2800_);
v___x_2803_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2802_);
v___x_2804_ = l_Lean_Syntax_isOfKind(v___x_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2802_);
v___x_2806_ = l_Lean_Syntax_isOfKind(v___x_2802_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
lean_dec(v___x_2802_);
v___x_2807_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_dec_ref_known(v___x_2807_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2807_;
}
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2808_ = l_Lean_Syntax_getArg(v___x_2802_, v___x_2800_);
v___x_2809_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2808_);
v___x_2810_ = l_Lean_Syntax_isOfKind(v___x_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
lean_dec(v___x_2808_);
lean_dec(v___x_2802_);
v___x_2811_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_dec_ref_known(v___x_2811_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2811_;
}
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2812_ = l_Lean_Syntax_getArg(v___x_2802_, v___x_2801_);
lean_dec(v___x_2802_);
v___x_2813_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2812_);
v___x_2814_ = l_Lean_Syntax_isOfKind(v___x_2812_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; 
lean_dec(v___x_2812_);
lean_dec(v___x_2808_);
v___x_2815_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_dec_ref_known(v___x_2815_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2815_;
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2817_, 0, v___x_2808_);
v___x_2818_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2817_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = l_Lean_Widget_elabWidgetInstanceSpec(v___x_2812_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_n(v_a_2821_, 2);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2821_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2822_) == 0)
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_unbox(v_a_2819_);
if (v___x_2823_ == 1)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; 
lean_dec(v_a_2821_);
lean_dec(v_a_2819_);
v_a_2824_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2825_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2824_, v___y_2784_, v___y_2786_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2825_;
}
}
else
{
lean_object* v_a_2826_; lean_object* v_id_2827_; uint64_t v_javascriptHash_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2826_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2822_, 1);
v_id_2827_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_id_2827_);
v_javascriptHash_2828_ = lean_ctor_get_uint64(v_a_2826_, sizeof(void*)*2);
lean_dec(v_a_2826_);
v___x_2829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1));
v___x_2830_ = l_Lean_Name_append(v_id_2827_, v___x_2829_);
v___x_2831_ = l_Lean_Core_mkFreshUserName(v___x_2830_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2821_, v___y_2784_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v___x_2853_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2853_ = l_Lean_Expr_hasMVar(v_a_2834_);
if (v___x_2853_ == 0)
{
v___y_2836_ = v___y_2781_;
v___y_2837_ = v___y_2782_;
v___y_2838_ = v___y_2783_;
v___y_2839_ = v___y_2784_;
v___y_2840_ = v___y_2785_;
v___y_2841_ = v___y_2786_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2834_);
v___x_2855_ = l_Lean_indentExpr(v_a_2834_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2856_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref_known(v___x_2857_, 1);
v___y_2836_ = v___y_2781_;
v___y_2837_ = v___y_2782_;
v___y_2838_ = v___y_2783_;
v___y_2839_ = v___y_2784_;
v___y_2840_ = v___y_2785_;
v___y_2841_ = v___y_2786_;
goto v___jp_2835_;
}
else
{
lean_dec(v_a_2834_);
lean_dec(v_a_2832_);
lean_dec(v_a_2819_);
return v___x_2857_;
}
}
v___jp_2835_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
lean_inc_n(v_a_2832_, 2);
v___x_2843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2843_, 0, v_a_2832_);
lean_ctor_set(v___x_2843_, 1, v___x_2816_);
lean_ctor_set(v___x_2843_, 2, v___x_2842_);
v___x_2844_ = lean_box(0);
v___x_2845_ = 1;
v___x_2846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2846_, 0, v_a_2832_);
lean_ctor_set(v___x_2846_, 1, v___x_2816_);
v___x_2847_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2843_);
lean_ctor_set(v___x_2847_, 1, v_a_2834_);
lean_ctor_set(v___x_2847_, 2, v___x_2844_);
lean_ctor_set(v___x_2847_, 3, v___x_2846_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*4, v___x_2845_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
v___x_2849_ = l_Lean_addAndCompile(v___x_2848_, v___x_2776_, v___x_2804_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2849_) == 0)
{
uint8_t v___x_2850_; 
lean_dec_ref_known(v___x_2849_, 1);
v___x_2850_ = lean_unbox(v_a_2819_);
lean_dec(v_a_2819_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_2828_, v_a_2832_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2851_;
}
}
else
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_2828_, v_a_2832_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_dec_ref_known(v___x_2852_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2852_;
}
}
}
else
{
lean_dec(v_a_2832_);
lean_dec(v_a_2819_);
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_a_2832_);
lean_dec(v_a_2819_);
v_a_2858_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2833_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2833_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2821_);
lean_dec(v_a_2819_);
v_a_2866_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2831_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2831_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2821_);
lean_dec(v_a_2819_);
v_a_2874_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2822_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2822_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_a_2819_);
v_a_2882_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2820_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2820_);
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
lean_dec(v___x_2812_);
v_a_2890_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2818_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2818_);
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
}
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2898_ = l_Lean_Syntax_getArg(v___x_2802_, v___x_2801_);
lean_dec(v___x_2802_);
v___x_2899_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2898_);
v___x_2900_ = l_Lean_Syntax_isOfKind(v___x_2898_, v___x_2899_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; 
lean_dec(v___x_2898_);
v___x_2901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_dec_ref_known(v___x_2901_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2901_;
}
}
else
{
lean_object* v_toCold_2902_; lean_object* v_ref_2903_; lean_object* v_quotContext_2904_; lean_object* v_currMacroScope_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_toCold_2902_ = lean_ctor_get(v___y_2785_, 0);
v_ref_2903_ = lean_ctor_get(v___y_2785_, 2);
v_quotContext_2904_ = lean_ctor_get(v_toCold_2902_, 8);
v_currMacroScope_2905_ = lean_ctor_get(v_toCold_2902_, 9);
v___x_2906_ = 0;
v___x_2907_ = l_Lean_SourceInfo_fromRef(v_ref_2903_, v___x_2906_);
v___x_2908_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2909_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2910_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2905_);
lean_inc(v_quotContext_2904_);
v___x_2911_ = l_Lean_addMacroScope(v_quotContext_2904_, v___x_2910_, v_currMacroScope_2905_);
v___x_2912_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2907_, 2);
v___x_2913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2907_);
lean_ctor_set(v___x_2913_, 1, v___x_2909_);
lean_ctor_set(v___x_2913_, 2, v___x_2911_);
lean_ctor_set(v___x_2913_, 3, v___x_2912_);
v___x_2914_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2915_ = l_Lean_Syntax_node1(v___x_2907_, v___x_2914_, v___x_2898_);
v___x_2916_ = l_Lean_Syntax_node2(v___x_2907_, v___x_2908_, v___x_2913_, v___x_2915_);
v___x_2917_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2918_ = l_Lean_Elab_Term_elabTerm(v___x_2916_, v___x_2917_, v___x_2776_, v___x_2776_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2920_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2919_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; uint64_t v_javascriptHash_2922_; lean_object* v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v_javascriptHash_2922_ = lean_ctor_get_uint64(v_a_2921_, sizeof(void*)*1);
lean_dec(v_a_2921_);
v___x_2923_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2922_, v___y_2784_, v___y_2786_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_dec_ref_known(v___x_2923_, 1);
v_a_2789_ = v___x_2796_;
goto v___jp_2788_;
}
else
{
return v___x_2923_;
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
v_a_2924_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2920_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2920_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2918_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2918_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
}
v___jp_2788_:
{
size_t v___x_2790_; size_t v___x_2791_; 
v___x_2790_ = ((size_t)1ULL);
v___x_2791_ = lean_usize_add(v_i_2779_, v___x_2790_);
v_i_2779_ = v___x_2791_;
v_b_2780_ = v_a_2789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2940_, lean_object* v_as_2941_, lean_object* v_sz_2942_, lean_object* v_i_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_30868__boxed_2952_; size_t v_sz_boxed_2953_; size_t v_i_boxed_2954_; lean_object* v_res_2955_; 
v___x_30868__boxed_2952_ = lean_unbox(v___x_2940_);
v_sz_boxed_2953_ = lean_unbox_usize(v_sz_2942_);
lean_dec(v_sz_2942_);
v_i_boxed_2954_ = lean_unbox_usize(v_i_2943_);
lean_dec(v_i_2943_);
v_res_2955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_30868__boxed_2952_, v_as_2941_, v_sz_boxed_2953_, v_i_boxed_2954_, v_b_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_as_2941_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2956_, lean_object* v___x_2957_, size_t v_sz_2958_, size_t v___x_2959_, lean_object* v___x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2956_, v___x_2957_, v_sz_2958_, v___x_2959_, v___x_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v___x_2968_, 0);
lean_dec(v_unused_2976_);
v___x_2970_ = v___x_2968_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v___x_2968_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2960_);
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2960_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
else
{
return v___x_2968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_2977_, lean_object* v___x_2978_, lean_object* v_sz_2979_, lean_object* v___x_2980_, lean_object* v___x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v___x_31220__boxed_2989_; size_t v_sz_boxed_2990_; size_t v___x_31222__boxed_2991_; lean_object* v_res_2992_; 
v___x_31220__boxed_2989_ = lean_unbox(v___x_2977_);
v_sz_boxed_2990_ = lean_unbox_usize(v_sz_2979_);
lean_dec(v_sz_2979_);
v___x_31222__boxed_2991_ = lean_unbox_usize(v___x_2980_);
lean_dec(v___x_2980_);
v_res_2992_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_31220__boxed_2989_, v___x_2978_, v_sz_boxed_2990_, v___x_31222__boxed_2991_, v___x_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v___x_2978_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_2995_);
v___x_3000_ = l_Lean_Syntax_isOfKind(v_x_2995_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_x_2995_);
v___x_3001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v_ws_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; size_t v_sz_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___f_3011_; lean_object* v___x_3012_; 
v___x_3002_ = lean_unsigned_to_nat(2u);
v___x_3003_ = l_Lean_Syntax_getArg(v_x_2995_, v___x_3002_);
lean_dec(v_x_2995_);
v_ws_3004_ = l_Lean_Syntax_getArgs(v___x_3003_);
lean_dec(v___x_3003_);
v___x_3005_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_3004_);
lean_dec_ref(v_ws_3004_);
v___x_3006_ = lean_box(0);
v_sz_3007_ = lean_array_size(v___x_3005_);
v___x_3008_ = lean_box(v___x_3000_);
v___x_3009_ = lean_box_usize(v_sz_3007_);
v___x_3010_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_3011_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3011_, 0, v___x_3008_);
lean_closure_set(v___f_3011_, 1, v___x_3005_);
lean_closure_set(v___f_3011_, 2, v___x_3009_);
lean_closure_set(v___f_3011_, 3, v___x_3010_);
lean_closure_set(v___f_3011_, 4, v___x_3006_);
v___x_3012_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3011_, v_a_2996_, v_a_2997_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_3013_, v_a_3014_, v_a_3015_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_3019_, v___y_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3023_, lean_object* v_x_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_3023_, v_x_3024_, v___y_3025_, v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_x_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_3028_, lean_object* v_ref_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_3029_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3038_, lean_object* v_ref_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3038_, v_ref_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3048_, lean_object* v_x_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3058_, v_x_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3068_, v___y_3072_, v___y_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3086_, lean_object* v_msg_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3096_, lean_object* v_msg_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3096_, v_msg_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3106_, v___y_3110_, v___y_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
uint64_t v_h_boxed_3123_; lean_object* v_res_3124_; 
v_h_boxed_3123_ = lean_unbox_uint64(v_h_3115_);
lean_dec_ref(v_h_3115_);
v_res_3124_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3123_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3125_, lean_object* v_msg_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3125_, v_msg_3126_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3135_, lean_object* v_msg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3135_, v_msg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3145_, lean_object* v_as_x27_3146_, lean_object* v_b_3147_, lean_object* v_a_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3146_, v_b_3147_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3157_, lean_object* v_as_x27_3158_, lean_object* v_b_3159_, lean_object* v_a_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3157_, v_as_x27_3158_, v_b_3159_, v_a_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v_as_x27_3158_);
lean_dec(v_as_3157_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3169_, lean_object* v_ref_3170_, lean_object* v_msg_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3170_, v_msg_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3180_, lean_object* v_ref_3181_, lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3180_, v_ref_3181_, v_msg_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v_ref_3181_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3191_, lean_object* v_t_3192_, uint64_t v_k_3193_, lean_object* v_fallback_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3192_, v_k_3193_, v_fallback_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3196_, lean_object* v_t_3197_, lean_object* v_k_3198_, lean_object* v_fallback_3199_){
_start:
{
uint64_t v_k_boxed_3200_; lean_object* v_res_3201_; 
v_k_boxed_3200_ = lean_unbox_uint64(v_k_3198_);
lean_dec_ref(v_k_3198_);
v_res_3201_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3196_, v_t_3197_, v_k_boxed_3200_, v_fallback_3199_);
lean_dec(v_fallback_3199_);
lean_dec(v_t_3197_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3202_, uint64_t v_k_3203_, lean_object* v_v_3204_, lean_object* v_t_3205_, lean_object* v_hl_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3203_, v_v_3204_, v_t_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3208_, lean_object* v_k_3209_, lean_object* v_v_3210_, lean_object* v_t_3211_, lean_object* v_hl_3212_){
_start:
{
uint64_t v_k_boxed_3213_; lean_object* v_res_3214_; 
v_k_boxed_3213_ = lean_unbox_uint64(v_k_3209_);
lean_dec_ref(v_k_3209_);
v_res_3214_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3208_, v_k_boxed_3213_, v_v_3210_, v_t_3211_, v_hl_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11_spec__16(lean_object* v_00_u03b2_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg___boxed(lean_object* v___dummy_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg();
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11(lean_object* v_00_u03b2_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(lean_object* v_00_u03b1_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_00_u03c3_3225_, lean_object* v_ext_3226_, lean_object* v_b_3227_, uint8_t v_kind_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v_ext_3226_, v_b_3227_, v_kind_3228_, v___y_3232_, v___y_3233_, v___y_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___boxed(lean_object* v_00_u03b1_3237_, lean_object* v_00_u03b2_3238_, lean_object* v_00_u03c3_3239_, lean_object* v_ext_3240_, lean_object* v_b_3241_, lean_object* v_kind_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
uint8_t v_kind_boxed_3250_; lean_object* v_res_3251_; 
v_kind_boxed_3250_ = lean_unbox(v_kind_3242_);
v_res_3251_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(v_00_u03b1_3237_, v_00_u03b2_3238_, v_00_u03c3_3239_, v_ext_3240_, v_b_3241_, v_kind_boxed_3250_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(lean_object* v_msgData_3252_, lean_object* v_macroStack_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_msgData_3252_, v_macroStack_3253_, v___y_3258_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___boxed(lean_object* v_msgData_3262_, lean_object* v_macroStack_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(v_msgData_3262_, v_macroStack_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(lean_object* v_00_u03b2_3272_, uint64_t v_k_3273_, lean_object* v_t_3274_, lean_object* v_h_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_3273_, v_t_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___boxed(lean_object* v_00_u03b2_3277_, lean_object* v_k_3278_, lean_object* v_t_3279_, lean_object* v_h_3280_){
_start:
{
uint64_t v_k_boxed_3281_; lean_object* v_res_3282_; 
v_k_boxed_3281_ = lean_unbox_uint64(v_k_3278_);
lean_dec_ref(v_k_3278_);
v_res_3282_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(v_00_u03b2_3277_, v_k_boxed_3281_, v_t_3279_, v_h_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3283_, lean_object* v_m_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3284_, v_a_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3287_, lean_object* v_m_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3287_, v_m_3288_, v_a_3289_);
lean_dec(v_a_3289_);
lean_dec_ref(v_m_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14(lean_object* v_00_u03b2_3291_, lean_object* v_x_3292_, lean_object* v_x_3293_){
_start:
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___redArg(v_x_3292_, v_x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
uint8_t v_res_3298_; lean_object* v_r_3299_; 
v_res_3298_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14(v_00_u03b2_3295_, v_x_3296_, v_x_3297_);
lean_dec_ref(v_x_3297_);
lean_dec_ref(v_x_3296_);
v_r_3299_ = lean_box(v_res_3298_);
return v_r_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17(lean_object* v_00_u03b2_3300_, lean_object* v_a_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___redArg(v_a_3301_, v_x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_a_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__17(v_00_u03b2_3304_, v_a_3305_, v_x_3306_);
lean_dec(v_x_3306_);
lean_dec(v_a_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26(lean_object* v_00_u03b2_3308_, lean_object* v_x_3309_, size_t v_x_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v___x_3312_; 
v___x_3312_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___redArg(v_x_3309_, v_x_3310_, v_x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
size_t v_x_31593__boxed_3317_; uint8_t v_res_3318_; lean_object* v_r_3319_; 
v_x_31593__boxed_3317_ = lean_unbox_usize(v_x_3315_);
lean_dec(v_x_3315_);
v_res_3318_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26(v_00_u03b2_3313_, v_x_3314_, v_x_31593__boxed_3317_, v_x_3316_);
lean_dec_ref(v_x_3316_);
lean_dec_ref(v_x_3314_);
v_r_3319_ = lean_box(v_res_3318_);
return v_r_3319_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30(lean_object* v_00_u03b2_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_heq_3323_, lean_object* v_i_3324_, lean_object* v_k_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___redArg(v_keys_3321_, v_i_3324_, v_k_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_keys_3328_, lean_object* v_vals_3329_, lean_object* v_heq_3330_, lean_object* v_i_3331_, lean_object* v_k_3332_){
_start:
{
uint8_t v_res_3333_; lean_object* v_r_3334_; 
v_res_3333_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__14_spec__26_spec__30(v_00_u03b2_3327_, v_keys_3328_, v_vals_3329_, v_heq_3330_, v_i_3331_, v_k_3332_);
lean_dec_ref(v_k_3332_);
lean_dec_ref(v_vals_3329_);
lean_dec_ref(v_keys_3328_);
v_r_3334_ = lean_box(v_res_3333_);
return v_r_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3352_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3362_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; uint64_t v_javascriptHash_3365_; lean_object* v_props_3366_; lean_object* v___x_3367_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v_javascriptHash_3365_ = lean_ctor_get_uint64(v_a_3364_, sizeof(void*)*2);
v_props_3366_ = lean_ctor_get(v_a_3364_, 1);
lean_inc_ref(v_props_3366_);
lean_dec(v_a_3364_);
v___x_3367_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3365_, v_props_3366_, v_x_3353_, v___y_3358_, v___y_3359_);
return v___x_3367_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v_x_3353_);
v_a_3368_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3363_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3363_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v_x_3353_);
v_a_3376_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3361_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3361_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3384_, v_x_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3398_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3394_);
v___x_3399_ = l_Lean_Syntax_isOfKind(v_x_3394_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec(v_x_3394_);
v___x_3400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v_s_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; 
v___x_3401_ = lean_unsigned_to_nat(1u);
v_s_3402_ = l_Lean_Syntax_getArg(v_x_3394_, v___x_3401_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3403_, 0, v_s_3402_);
lean_closure_set(v___f_3403_, 1, v_x_3394_);
v___x_3404_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3403_, v_a_3395_, v_a_3396_);
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_Widget_elabWidgetCmd(v_x_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
return v_res_3409_;
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
