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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
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
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_56_ = l_Array_mkArray0(lean_box(0));
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
lean_object* v_ref_235_; lean_object* v_quotContext_236_; lean_object* v_currMacroScope_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___y_260_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_ref_235_ = lean_ctor_get(v_a_232_, 5);
v_quotContext_236_ = lean_ctor_get(v_a_232_, 10);
v_currMacroScope_237_ = lean_ctor_get(v_a_232_, 11);
v___x_238_ = 0;
v___x_239_ = l_Lean_SourceInfo_fromRef(v_ref_235_, v___x_238_);
v___x_240_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3));
v___x_241_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4));
lean_inc_n(v___x_239_, 5);
v___x_242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_244_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
v___x_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_239_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
v___x_246_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9));
v___x_247_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11));
v___x_248_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13));
v___x_249_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15);
v___x_250_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16));
lean_inc(v_currMacroScope_237_);
lean_inc(v_quotContext_236_);
v___x_251_ = l_Lean_addMacroScope(v_quotContext_236_, v___x_250_, v_currMacroScope_237_);
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18));
v___x_254_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_254_, 0, v___x_239_);
lean_ctor_set(v___x_254_, 1, v___x_249_);
lean_ctor_set(v___x_254_, 2, v___x_251_);
lean_ctor_set(v___x_254_, 3, v___x_253_);
lean_inc_ref(v___x_245_);
v___x_255_ = l_Lean_Syntax_node2(v___x_239_, v___x_248_, v___x_254_, v___x_245_);
v___x_256_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20));
v___x_257_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21));
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_239_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_324_ = l_Lean_TSyntax_getId(v_mod_226_);
lean_inc(v___x_324_);
v___x_325_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_252_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_quoteNameMk(v___x_324_);
v___y_260_ = v___x_326_;
goto v___jp_259_;
}
else
{
lean_object* v_val_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___x_324_);
v_val_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_325_, 1);
v___x_328_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79));
v___x_329_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80));
v___x_330_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58));
v___x_331_ = lean_string_intercalate(v___x_330_, v_val_327_);
v___x_332_ = lean_string_append(v___x_329_, v___x_331_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_box(2);
v___x_334_ = l_Lean_Syntax_mkNameLit(v___x_332_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_array_push(v___x_336_, v___x_334_);
v___x_338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_338_, 0, v___x_333_);
lean_ctor_set(v___x_338_, 1, v___x_328_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
v___y_260_ = v___x_338_;
goto v___jp_259_;
}
v___jp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; 
lean_inc_ref_n(v___x_245_, 15);
lean_inc_ref_n(v___x_258_, 2);
lean_inc_n(v___x_239_, 31);
v___x_261_ = l_Lean_Syntax_node3(v___x_239_, v___x_256_, v___x_258_, v___x_245_, v___y_260_);
v___x_262_ = l_Lean_Syntax_node3(v___x_239_, v___x_243_, v___x_245_, v___x_245_, v___x_261_);
v___x_263_ = l_Lean_Syntax_node2(v___x_239_, v___x_247_, v___x_255_, v___x_262_);
v___x_264_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23);
v___x_265_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24));
lean_inc_n(v_currMacroScope_237_, 5);
lean_inc_n(v_quotContext_236_, 5);
v___x_266_ = l_Lean_addMacroScope(v_quotContext_236_, v___x_265_, v_currMacroScope_237_);
v___x_267_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_267_, 0, v___x_239_);
lean_ctor_set(v___x_267_, 1, v___x_264_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_ctor_set(v___x_267_, 3, v___x_252_);
lean_inc_ref(v___x_267_);
v___x_268_ = l_Lean_Syntax_node2(v___x_239_, v___x_248_, v___x_267_, v___x_245_);
v___x_269_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26));
v___x_270_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28));
v___x_271_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30));
v___x_272_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31));
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_239_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33));
v___x_275_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35);
v___x_276_ = lean_box(0);
v___x_277_ = l_Lean_addMacroScope(v_quotContext_236_, v___x_276_, v_currMacroScope_237_);
v___x_278_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46));
v___x_279_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_279_, 0, v___x_239_);
lean_ctor_set(v___x_279_, 1, v___x_275_);
lean_ctor_set(v___x_279_, 2, v___x_277_);
lean_ctor_set(v___x_279_, 3, v___x_278_);
v___x_280_ = l_Lean_Syntax_node1(v___x_239_, v___x_274_, v___x_279_);
v___x_281_ = l_Lean_Syntax_node2(v___x_239_, v___x_271_, v___x_273_, v___x_280_);
v___x_282_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_283_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_284_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
v___x_285_ = l_Lean_addMacroScope(v_quotContext_236_, v___x_284_, v_currMacroScope_237_);
v___x_286_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
v___x_287_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_287_, 0, v___x_239_);
lean_ctor_set(v___x_287_, 1, v___x_283_);
lean_ctor_set(v___x_287_, 2, v___x_285_);
lean_ctor_set(v___x_287_, 3, v___x_286_);
v___x_288_ = l_Lean_Syntax_node1(v___x_239_, v___x_243_, v_mod_226_);
v___x_289_ = l_Lean_Syntax_node2(v___x_239_, v___x_282_, v___x_287_, v___x_288_);
v___x_290_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57));
v___x_291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_239_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_Syntax_node3(v___x_239_, v___x_270_, v___x_281_, v___x_289_, v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58));
v___x_294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_239_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_Syntax_node3(v___x_239_, v___x_269_, v___x_292_, v___x_294_, v___x_267_);
v___x_296_ = l_Lean_Syntax_node3(v___x_239_, v___x_256_, v___x_258_, v___x_245_, v___x_295_);
v___x_297_ = l_Lean_Syntax_node3(v___x_239_, v___x_243_, v___x_245_, v___x_245_, v___x_296_);
v___x_298_ = l_Lean_Syntax_node2(v___x_239_, v___x_247_, v___x_268_, v___x_297_);
v___x_299_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60);
v___x_300_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61));
v___x_301_ = l_Lean_addMacroScope(v_quotContext_236_, v___x_300_, v_currMacroScope_237_);
v___x_302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_302_, 0, v___x_239_);
lean_ctor_set(v___x_302_, 1, v___x_299_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
lean_ctor_set(v___x_302_, 3, v___x_252_);
v___x_303_ = l_Lean_Syntax_node2(v___x_239_, v___x_248_, v___x_302_, v___x_245_);
v___x_304_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63);
v___x_305_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67));
v___x_306_ = l_Lean_addMacroScope(v_quotContext_236_, v___x_305_, v_currMacroScope_237_);
v___x_307_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70));
v___x_308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_308_, 0, v___x_239_);
lean_ctor_set(v___x_308_, 1, v___x_304_);
lean_ctor_set(v___x_308_, 2, v___x_306_);
lean_ctor_set(v___x_308_, 3, v___x_307_);
v___x_309_ = l_Lean_Syntax_node1(v___x_239_, v___x_243_, v_props_227_);
v___x_310_ = l_Lean_Syntax_node2(v___x_239_, v___x_282_, v___x_308_, v___x_309_);
v___x_311_ = l_Lean_Syntax_node3(v___x_239_, v___x_256_, v___x_258_, v___x_245_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node3(v___x_239_, v___x_243_, v___x_245_, v___x_245_, v___x_311_);
v___x_313_ = l_Lean_Syntax_node2(v___x_239_, v___x_247_, v___x_303_, v___x_312_);
v___x_314_ = l_Lean_Syntax_node5(v___x_239_, v___x_243_, v___x_263_, v___x_245_, v___x_298_, v___x_245_, v___x_313_);
v___x_315_ = l_Lean_Syntax_node1(v___x_239_, v___x_246_, v___x_314_);
v___x_316_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72));
v___x_317_ = l_Lean_Syntax_node1(v___x_239_, v___x_316_, v___x_245_);
v___x_318_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73));
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_239_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Lean_Syntax_node6(v___x_239_, v___x_240_, v___x_242_, v___x_245_, v___x_315_, v___x_317_, v___x_245_, v___x_319_);
v___x_321_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77);
v___x_322_ = 1;
v___x_323_ = l_Lean_Elab_Term_elabTerm(v___x_320_, v___x_321_, v___x_322_, v___x_322_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___boxed(lean_object* v_mod_339_, lean_object* v_props_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_339_, v_props_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_348_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_box(0);
v___x_350_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg(){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___boxed(lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(lean_object* v_00_u03b1_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___boxed(lean_object* v_00_u03b1_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(v_00_u03b1_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__0));
v___x_377_ = l_String_toRawSubstring_x27(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec(lean_object* v_x_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v_x_398_);
v___x_407_ = l_Lean_Syntax_isOfKind(v_x_398_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec(v_x_398_);
v___x_408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v_mod_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v_mod_410_ = l_Lean_Syntax_getArg(v_x_398_, v___x_409_);
v___x_411_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v_mod_410_);
v___x_412_ = l_Lean_Syntax_isOfKind(v_mod_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec(v_mod_410_);
lean_dec(v_x_398_);
v___x_413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = l_Lean_Syntax_getArg(v_x_398_, v___x_414_);
lean_dec(v_x_398_);
lean_inc(v___x_415_);
v___x_416_ = l_Lean_Syntax_matchesNull(v___x_415_, v___x_409_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_415_);
v___x_418_ = l_Lean_Syntax_matchesNull(v___x_415_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v___x_415_);
lean_dec(v_mod_410_);
v___x_419_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_419_;
}
else
{
lean_object* v_props_420_; lean_object* v___x_421_; 
v_props_420_ = l_Lean_Syntax_getArg(v___x_415_, v___x_414_);
lean_dec(v___x_415_);
v___x_421_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_410_, v_props_420_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_421_;
}
}
else
{
lean_object* v_ref_422_; lean_object* v_quotContext_423_; lean_object* v_currMacroScope_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_415_);
v_ref_422_ = lean_ctor_get(v_a_403_, 5);
v_quotContext_423_ = lean_ctor_get(v_a_403_, 10);
v_currMacroScope_424_ = lean_ctor_get(v_a_403_, 11);
v___x_425_ = 0;
v___x_426_ = l_Lean_SourceInfo_fromRef(v_ref_422_, v___x_425_);
v___x_427_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_428_ = lean_obj_once(&l_Lean_Widget_elabWidgetInstanceSpec___closed__1, &l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once, _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1);
v___x_429_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__4));
lean_inc(v_currMacroScope_424_);
lean_inc(v_quotContext_423_);
v___x_430_ = l_Lean_addMacroScope(v_quotContext_423_, v___x_429_, v_currMacroScope_424_);
v___x_431_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__7));
lean_inc_n(v___x_426_, 6);
v___x_432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_426_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
v___x_433_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_434_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__9));
v___x_435_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__10));
v___x_436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_426_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
v___x_438_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_438_, 0, v___x_426_);
lean_ctor_set(v___x_438_, 1, v___x_433_);
lean_ctor_set(v___x_438_, 2, v___x_437_);
v___x_439_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__11));
v___x_440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_426_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_Syntax_node3(v___x_426_, v___x_434_, v___x_436_, v___x_438_, v___x_440_);
v___x_442_ = l_Lean_Syntax_node1(v___x_426_, v___x_433_, v___x_441_);
v___x_443_ = l_Lean_Syntax_node2(v___x_426_, v___x_427_, v___x_432_, v___x_442_);
v___x_444_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_410_, v___x_443_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec___boxed(lean_object* v_x_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Widget_elabWidgetInstanceSpec(v_x_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg___boxed(lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(lean_object* v_00_u03b1_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___boxed(lean_object* v_00_u03b1_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(v_00_u03b1_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(lean_object* v_e_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = l_Lean_Expr_hasMVar(v_e_562_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_e_562_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v_mctx_568_; lean_object* v___x_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; lean_object* v_cache_573_; lean_object* v_zetaDeltaFVarIds_574_; lean_object* v_postponed_575_; lean_object* v_diag_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_585_; 
v___x_567_ = lean_st_ref_get(v___y_563_);
v_mctx_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_mctx_568_);
lean_dec(v___x_567_);
v___x_569_ = l_Lean_instantiateMVarsCore(v_mctx_568_, v_e_562_);
v_fst_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_snd_571_);
lean_dec_ref(v___x_569_);
v___x_572_ = lean_st_ref_take(v___y_563_);
v_cache_573_ = lean_ctor_get(v___x_572_, 1);
v_zetaDeltaFVarIds_574_ = lean_ctor_get(v___x_572_, 2);
v_postponed_575_ = lean_ctor_get(v___x_572_, 3);
v_diag_576_ = lean_ctor_get(v___x_572_, 4);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_586_);
v___x_578_ = v___x_572_;
v_isShared_579_ = v_isSharedCheck_585_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_diag_576_);
lean_inc(v_postponed_575_);
lean_inc(v_zetaDeltaFVarIds_574_);
lean_inc(v_cache_573_);
lean_dec(v___x_572_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_585_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_snd_571_);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_snd_571_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_cache_573_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_zetaDeltaFVarIds_574_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_postponed_575_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_diag_576_);
v___x_581_ = v_reuseFailAlloc_584_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_st_ref_put(v___y_563_, v___x_581_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_fst_570_);
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(lean_object* v_e_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_587_, v___y_588_);
lean_dec(v___y_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(lean_object* v_e_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_591_, v___y_595_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(lean_object* v_e_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(v_e_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(uint64_t v_k_609_, lean_object* v_t_610_){
_start:
{
if (lean_obj_tag(v_t_610_) == 0)
{
lean_object* v_k_611_; lean_object* v_v_612_; lean_object* v_l_613_; lean_object* v_r_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_1271_; 
v_k_611_ = lean_ctor_get(v_t_610_, 1);
v_v_612_ = lean_ctor_get(v_t_610_, 2);
v_l_613_ = lean_ctor_get(v_t_610_, 3);
v_r_614_ = lean_ctor_get(v_t_610_, 4);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_t_610_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_t_610_, 0);
lean_dec(v_unused_1272_);
v___x_616_ = v_t_610_;
v_isShared_617_ = v_isSharedCheck_1271_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_r_614_);
lean_inc(v_l_613_);
lean_inc(v_v_612_);
lean_inc(v_k_611_);
lean_dec(v_t_610_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_1271_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint64_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unbox_uint64(v_k_611_);
v___x_619_ = lean_uint64_dec_lt(v_k_609_, v___x_618_);
if (v___x_619_ == 0)
{
uint64_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unbox_uint64(v_k_611_);
v___x_621_ = lean_uint64_dec_eq(v_k_609_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v_impl_622_; lean_object* v___x_623_; 
v_impl_622_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_609_, v_r_614_);
v___x_623_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_622_) == 0)
{
if (lean_obj_tag(v_l_613_) == 0)
{
lean_object* v_size_624_; lean_object* v_size_625_; lean_object* v_k_626_; lean_object* v_v_627_; lean_object* v_l_628_; lean_object* v_r_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_size_624_ = lean_ctor_get(v_impl_622_, 0);
lean_inc(v_size_624_);
v_size_625_ = lean_ctor_get(v_l_613_, 0);
v_k_626_ = lean_ctor_get(v_l_613_, 1);
v_v_627_ = lean_ctor_get(v_l_613_, 2);
v_l_628_ = lean_ctor_get(v_l_613_, 3);
v_r_629_ = lean_ctor_get(v_l_613_, 4);
lean_inc(v_r_629_);
v___x_630_ = lean_unsigned_to_nat(3u);
v___x_631_ = lean_nat_mul(v___x_630_, v_size_624_);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v_size_625_);
lean_dec(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_r_629_);
v___x_633_ = lean_nat_add(v___x_623_, v_size_625_);
v___x_634_ = lean_nat_add(v___x_633_, v_size_624_);
lean_dec(v_size_624_);
lean_dec(v___x_633_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_impl_622_);
lean_ctor_set(v___x_616_, 0, v___x_634_);
v___x_636_ = v___x_616_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_l_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_impl_622_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_703_; 
lean_inc(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_inc(v_size_625_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; 
v_unused_704_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_l_613_, 2);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_l_613_, 1);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_708_);
v___x_639_ = v_l_613_;
v_isShared_640_ = v_isSharedCheck_703_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_l_613_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_703_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_size_641_; lean_object* v_size_642_; lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_size_641_ = lean_ctor_get(v_l_628_, 0);
v_size_642_ = lean_ctor_get(v_r_629_, 0);
v_k_643_ = lean_ctor_get(v_r_629_, 1);
v_v_644_ = lean_ctor_get(v_r_629_, 2);
v_l_645_ = lean_ctor_get(v_r_629_, 3);
v_r_646_ = lean_ctor_get(v_r_629_, 4);
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_nat_mul(v___x_647_, v_size_641_);
v___x_649_ = lean_nat_dec_lt(v_size_642_, v___x_648_);
lean_dec(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_r_646_);
lean_inc(v_l_645_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_r_629_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_679_ = lean_ctor_get(v_r_629_, 4);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_r_629_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_r_629_, 2);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_r_629_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_629_, 0);
lean_dec(v_unused_683_);
v___x_651_ = v_r_629_;
v_isShared_652_ = v_isSharedCheck_678_;
goto v_resetjp_650_;
}
else
{
lean_dec(v_r_629_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_678_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___x_666_; lean_object* v___y_668_; 
v___x_653_ = lean_nat_add(v___x_623_, v_size_625_);
lean_dec(v_size_625_);
v___x_654_ = lean_nat_add(v___x_653_, v_size_624_);
lean_dec(v___x_653_);
v___x_666_ = lean_nat_add(v___x_623_, v_size_641_);
if (lean_obj_tag(v_l_645_) == 0)
{
lean_object* v_size_676_; 
v_size_676_ = lean_ctor_get(v_l_645_, 0);
lean_inc(v_size_676_);
v___y_668_ = v_size_676_;
goto v___jp_667_;
}
else
{
lean_object* v___x_677_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___y_668_ = v___x_677_;
goto v___jp_667_;
}
v___jp_655_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_nat_add(v___y_656_, v___y_658_);
lean_dec(v___y_658_);
lean_dec(v___y_656_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_impl_622_);
lean_ctor_set(v___x_651_, 3, v_r_646_);
lean_ctor_set(v___x_651_, 2, v_v_612_);
lean_ctor_set(v___x_651_, 1, v_k_611_);
lean_ctor_set(v___x_651_, 0, v___x_659_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_impl_622_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 4, v___x_661_);
lean_ctor_set(v___x_639_, 3, v___y_657_);
lean_ctor_set(v___x_639_, 2, v_v_644_);
lean_ctor_set(v___x_639_, 1, v_k_643_);
lean_ctor_set(v___x_639_, 0, v___x_654_);
v___x_663_ = v___x_639_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v___y_657_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
v___jp_667_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_nat_add(v___x_666_, v___y_668_);
lean_dec(v___y_668_);
lean_dec(v___x_666_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_l_645_);
lean_ctor_set(v___x_616_, 3, v_l_628_);
lean_ctor_set(v___x_616_, 2, v_v_627_);
lean_ctor_set(v___x_616_, 1, v_k_626_);
lean_ctor_set(v___x_616_, 0, v___x_669_);
v___x_671_ = v___x_616_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_l_645_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_nat_add(v___x_623_, v_size_624_);
lean_dec(v_size_624_);
if (lean_obj_tag(v_r_646_) == 0)
{
lean_object* v_size_673_; 
v_size_673_ = lean_ctor_get(v_r_646_, 0);
lean_inc(v_size_673_);
v___y_656_ = v___x_672_;
v___y_657_ = v___x_671_;
v___y_658_ = v_size_673_;
goto v___jp_655_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___y_656_ = v___x_672_;
v___y_657_ = v___x_671_;
v___y_658_ = v___x_674_;
goto v___jp_655_;
}
}
}
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
lean_del_object(v___x_616_);
v___x_684_ = lean_nat_add(v___x_623_, v_size_625_);
lean_dec(v_size_625_);
v___x_685_ = lean_nat_add(v___x_684_, v_size_624_);
lean_dec(v___x_684_);
v___x_686_ = lean_nat_add(v___x_623_, v_size_624_);
lean_dec(v_size_624_);
v___x_687_ = lean_nat_add(v___x_686_, v_size_642_);
lean_dec(v___x_686_);
lean_inc_ref(v_impl_622_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 4, v_impl_622_);
lean_ctor_set(v___x_639_, 3, v_r_629_);
lean_ctor_set(v___x_639_, 2, v_v_612_);
lean_ctor_set(v___x_639_, 1, v_k_611_);
lean_ctor_set(v___x_639_, 0, v___x_687_);
v___x_689_ = v___x_639_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_impl_622_);
v___x_689_ = v_reuseFailAlloc_702_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_isSharedCheck_696_ = !lean_is_exclusive(v_impl_622_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_697_ = lean_ctor_get(v_impl_622_, 4);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_impl_622_, 3);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_impl_622_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_impl_622_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_impl_622_, 0);
lean_dec(v_unused_701_);
v___x_691_ = v_impl_622_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_impl_622_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 4, v___x_689_);
lean_ctor_set(v___x_691_, 3, v_l_628_);
lean_ctor_set(v___x_691_, 2, v_v_627_);
lean_ctor_set(v___x_691_, 1, v_k_626_);
lean_ctor_set(v___x_691_, 0, v___x_685_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v_size_709_ = lean_ctor_get(v_impl_622_, 0);
lean_inc(v_size_709_);
v___x_710_ = lean_nat_add(v___x_623_, v_size_709_);
lean_dec(v_size_709_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_impl_622_);
lean_ctor_set(v___x_616_, 0, v___x_710_);
v___x_712_ = v___x_616_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_l_613_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_impl_622_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
if (lean_obj_tag(v_l_613_) == 0)
{
lean_object* v_l_714_; 
v_l_714_ = lean_ctor_get(v_l_613_, 3);
if (lean_obj_tag(v_l_714_) == 0)
{
lean_object* v_r_715_; 
lean_inc_ref(v_l_714_);
v_r_715_ = lean_ctor_get(v_l_613_, 4);
lean_inc(v_r_715_);
if (lean_obj_tag(v_r_715_) == 0)
{
lean_object* v_size_716_; lean_object* v_k_717_; lean_object* v_v_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_731_; 
v_size_716_ = lean_ctor_get(v_l_613_, 0);
v_k_717_ = lean_ctor_get(v_l_613_, 1);
v_v_718_ = lean_ctor_get(v_l_613_, 2);
v_isSharedCheck_731_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; 
v_unused_732_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_733_);
v___x_720_ = v_l_613_;
v_isShared_721_ = v_isSharedCheck_731_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_v_718_);
lean_inc(v_k_717_);
lean_inc(v_size_716_);
lean_dec(v_l_613_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_731_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_size_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v_size_722_ = lean_ctor_get(v_r_715_, 0);
v___x_723_ = lean_nat_add(v___x_623_, v_size_716_);
lean_dec(v_size_716_);
v___x_724_ = lean_nat_add(v___x_623_, v_size_722_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 4, v_impl_622_);
lean_ctor_set(v___x_720_, 3, v_r_715_);
lean_ctor_set(v___x_720_, 2, v_v_612_);
lean_ctor_set(v___x_720_, 1, v_k_611_);
lean_ctor_set(v___x_720_, 0, v___x_724_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_r_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_impl_622_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_726_);
lean_ctor_set(v___x_616_, 3, v_l_714_);
lean_ctor_set(v___x_616_, 2, v_v_718_);
lean_ctor_set(v___x_616_, 1, v_k_717_);
lean_ctor_set(v___x_616_, 0, v___x_723_);
v___x_728_ = v___x_616_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_v_718_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_l_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_k_734_; lean_object* v_v_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_746_; 
v_k_734_ = lean_ctor_get(v_l_613_, 1);
v_v_735_ = lean_ctor_get(v_l_613_, 2);
v_isSharedCheck_746_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; lean_object* v_unused_749_; 
v_unused_747_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_749_);
v___x_737_ = v_l_613_;
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_v_735_);
lean_inc(v_k_734_);
lean_dec(v_l_613_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(3u);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 3, v_r_715_);
lean_ctor_set(v___x_737_, 2, v_v_612_);
lean_ctor_set(v___x_737_, 1, v_k_611_);
lean_ctor_set(v___x_737_, 0, v___x_623_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_r_715_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_r_715_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_741_);
lean_ctor_set(v___x_616_, 3, v_l_714_);
lean_ctor_set(v___x_616_, 2, v_v_735_);
lean_ctor_set(v___x_616_, 1, v_k_734_);
lean_ctor_set(v___x_616_, 0, v___x_739_);
v___x_743_ = v___x_616_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_735_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_l_714_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_r_750_; 
v_r_750_ = lean_ctor_get(v_l_613_, 4);
lean_inc(v_r_750_);
if (lean_obj_tag(v_r_750_) == 0)
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_775_; 
lean_inc(v_l_714_);
v_k_751_ = lean_ctor_get(v_l_613_, 1);
v_v_752_ = lean_ctor_get(v_l_613_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_776_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_778_);
v___x_754_ = v_l_613_;
v_isShared_755_ = v_isSharedCheck_775_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_v_752_);
lean_inc(v_k_751_);
lean_dec(v_l_613_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_775_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_k_756_; lean_object* v_v_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_771_; 
v_k_756_ = lean_ctor_get(v_r_750_, 1);
v_v_757_ = lean_ctor_get(v_r_750_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v_r_750_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; 
v_unused_772_ = lean_ctor_get(v_r_750_, 4);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_r_750_, 3);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_750_, 0);
lean_dec(v_unused_774_);
v___x_759_ = v_r_750_;
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_v_757_);
lean_inc(v_k_756_);
lean_dec(v_r_750_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(3u);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 4, v_l_714_);
lean_ctor_set(v___x_759_, 3, v_l_714_);
lean_ctor_set(v___x_759_, 2, v_v_752_);
lean_ctor_set(v___x_759_, 1, v_k_751_);
lean_ctor_set(v___x_759_, 0, v___x_623_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_l_714_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_l_714_);
v___x_763_ = v_reuseFailAlloc_770_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 4, v_l_714_);
lean_ctor_set(v___x_754_, 2, v_v_612_);
lean_ctor_set(v___x_754_, 1, v_k_611_);
lean_ctor_set(v___x_754_, 0, v___x_623_);
v___x_765_ = v___x_754_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_l_714_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_l_714_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_765_);
lean_ctor_set(v___x_616_, 3, v___x_763_);
lean_ctor_set(v___x_616_, 2, v_v_757_);
lean_ctor_set(v___x_616_, 1, v_k_756_);
lean_ctor_set(v___x_616_, 0, v___x_761_);
v___x_767_ = v___x_616_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_k_756_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_v_757_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_unsigned_to_nat(2u);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_r_750_);
lean_ctor_set(v___x_616_, 0, v___x_779_);
v___x_781_ = v___x_616_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_l_613_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_r_750_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v___x_784_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_l_613_);
lean_ctor_set(v___x_616_, 0, v___x_623_);
v___x_784_ = v___x_616_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v_l_613_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v_l_613_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_del_object(v___x_616_);
lean_dec(v_v_612_);
lean_dec(v_k_611_);
if (lean_obj_tag(v_l_613_) == 0)
{
if (lean_obj_tag(v_r_614_) == 0)
{
lean_object* v_size_786_; lean_object* v_k_787_; lean_object* v_v_788_; lean_object* v_l_789_; lean_object* v_r_790_; lean_object* v_size_791_; lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_l_794_; lean_object* v_r_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_size_786_ = lean_ctor_get(v_l_613_, 0);
v_k_787_ = lean_ctor_get(v_l_613_, 1);
v_v_788_ = lean_ctor_get(v_l_613_, 2);
v_l_789_ = lean_ctor_get(v_l_613_, 3);
v_r_790_ = lean_ctor_get(v_l_613_, 4);
lean_inc(v_r_790_);
v_size_791_ = lean_ctor_get(v_r_614_, 0);
v_k_792_ = lean_ctor_get(v_r_614_, 1);
v_v_793_ = lean_ctor_get(v_r_614_, 2);
v_l_794_ = lean_ctor_get(v_r_614_, 3);
lean_inc(v_l_794_);
v_r_795_ = lean_ctor_get(v_r_614_, 4);
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_dec_lt(v_size_786_, v_size_791_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_933_; 
lean_inc(v_l_789_);
lean_inc(v_v_788_);
lean_inc(v_k_787_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; 
v_unused_934_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_l_613_, 2);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_l_613_, 1);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_938_);
v___x_799_ = v_l_613_;
v_isShared_800_ = v_isSharedCheck_933_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_l_613_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_933_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v_tree_802_; 
v___x_801_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_787_, v_v_788_, v_l_789_, v_r_790_);
v_tree_802_ = lean_ctor_get(v___x_801_, 2);
lean_inc(v_tree_802_);
if (lean_obj_tag(v_tree_802_) == 0)
{
lean_object* v_k_803_; lean_object* v_v_804_; lean_object* v_size_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_k_803_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_k_803_);
v_v_804_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_v_804_);
lean_dec_ref(v___x_801_);
v_size_805_ = lean_ctor_get(v_tree_802_, 0);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_mul(v___x_806_, v_size_805_);
v___x_808_ = lean_nat_dec_lt(v___x_807_, v_size_791_);
lean_dec(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_l_794_);
v___x_809_ = lean_nat_add(v___x_796_, v_size_805_);
v___x_810_ = lean_nat_add(v___x_809_, v_size_791_);
lean_dec(v___x_809_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_614_);
lean_ctor_set(v___x_799_, 3, v_tree_802_);
lean_ctor_set(v___x_799_, 2, v_v_804_);
lean_ctor_set(v___x_799_, 1, v_k_803_);
lean_ctor_set(v___x_799_, 0, v___x_810_);
v___x_812_ = v___x_799_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_tree_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_r_614_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_868_; 
lean_inc(v_r_795_);
lean_inc(v_v_793_);
lean_inc(v_k_792_);
lean_inc(v_size_791_);
v_isSharedCheck_868_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_869_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_r_614_, 2);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_r_614_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_r_614_, 0);
lean_dec(v_unused_873_);
v___x_815_ = v_r_614_;
v_isShared_816_ = v_isSharedCheck_868_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_r_614_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_868_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_size_817_; lean_object* v_k_818_; lean_object* v_v_819_; lean_object* v_l_820_; lean_object* v_r_821_; lean_object* v_size_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_size_817_ = lean_ctor_get(v_l_794_, 0);
v_k_818_ = lean_ctor_get(v_l_794_, 1);
v_v_819_ = lean_ctor_get(v_l_794_, 2);
v_l_820_ = lean_ctor_get(v_l_794_, 3);
v_r_821_ = lean_ctor_get(v_l_794_, 4);
v_size_822_ = lean_ctor_get(v_r_795_, 0);
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = lean_nat_mul(v___x_823_, v_size_822_);
v___x_825_ = lean_nat_dec_lt(v_size_817_, v___x_824_);
lean_dec(v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_853_; 
lean_inc(v_r_821_);
lean_inc(v_l_820_);
lean_inc(v_v_819_);
lean_inc(v_k_818_);
v_isSharedCheck_853_ = !lean_is_exclusive(v_l_794_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; 
v_unused_854_ = lean_ctor_get(v_l_794_, 4);
lean_dec(v_unused_854_);
v_unused_855_ = lean_ctor_get(v_l_794_, 3);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_l_794_, 2);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_l_794_, 1);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_l_794_, 0);
lean_dec(v_unused_858_);
v___x_827_ = v_l_794_;
v_isShared_828_ = v_isSharedCheck_853_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_l_794_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_853_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_843_; 
v___x_829_ = lean_nat_add(v___x_796_, v_size_805_);
v___x_830_ = lean_nat_add(v___x_829_, v_size_791_);
lean_dec(v_size_791_);
if (lean_obj_tag(v_l_820_) == 0)
{
lean_object* v_size_851_; 
v_size_851_ = lean_ctor_get(v_l_820_, 0);
lean_inc(v_size_851_);
v___y_843_ = v_size_851_;
goto v___jp_842_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = lean_unsigned_to_nat(0u);
v___y_843_ = v___x_852_;
goto v___jp_842_;
}
v___jp_831_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_nat_add(v___y_832_, v___y_834_);
lean_dec(v___y_834_);
lean_dec(v___y_832_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 4, v_r_795_);
lean_ctor_set(v___x_827_, 3, v_r_821_);
lean_ctor_set(v___x_827_, 2, v_v_793_);
lean_ctor_set(v___x_827_, 1, v_k_792_);
lean_ctor_set(v___x_827_, 0, v___x_835_);
v___x_837_ = v___x_827_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_r_821_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_r_795_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v___x_837_);
lean_ctor_set(v___x_815_, 3, v___y_833_);
lean_ctor_set(v___x_815_, 2, v_v_819_);
lean_ctor_set(v___x_815_, 1, v_k_818_);
lean_ctor_set(v___x_815_, 0, v___x_830_);
v___x_839_ = v___x_815_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_818_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_819_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v___y_833_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
v___jp_842_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_nat_add(v___x_829_, v___y_843_);
lean_dec(v___y_843_);
lean_dec(v___x_829_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_l_820_);
lean_ctor_set(v___x_799_, 3, v_tree_802_);
lean_ctor_set(v___x_799_, 2, v_v_804_);
lean_ctor_set(v___x_799_, 1, v_k_803_);
lean_ctor_set(v___x_799_, 0, v___x_844_);
v___x_846_ = v___x_799_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_tree_802_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_l_820_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; 
v___x_847_ = lean_nat_add(v___x_796_, v_size_822_);
if (lean_obj_tag(v_r_821_) == 0)
{
lean_object* v_size_848_; 
v_size_848_ = lean_ctor_get(v_r_821_, 0);
lean_inc(v_size_848_);
v___y_832_ = v___x_847_;
v___y_833_ = v___x_846_;
v___y_834_ = v_size_848_;
goto v___jp_831_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___y_832_ = v___x_847_;
v___y_833_ = v___x_846_;
v___y_834_ = v___x_849_;
goto v___jp_831_;
}
}
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_859_ = lean_nat_add(v___x_796_, v_size_805_);
v___x_860_ = lean_nat_add(v___x_859_, v_size_791_);
lean_dec(v_size_791_);
v___x_861_ = lean_nat_add(v___x_859_, v_size_817_);
lean_dec(v___x_859_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v_l_794_);
lean_ctor_set(v___x_815_, 3, v_tree_802_);
lean_ctor_set(v___x_815_, 2, v_v_804_);
lean_ctor_set(v___x_815_, 1, v_k_803_);
lean_ctor_set(v___x_815_, 0, v___x_861_);
v___x_863_ = v___x_815_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_tree_802_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_l_794_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_795_);
lean_ctor_set(v___x_799_, 3, v___x_863_);
lean_ctor_set(v___x_799_, 2, v_v_793_);
lean_ctor_set(v___x_799_, 1, v_k_792_);
lean_ctor_set(v___x_799_, 0, v___x_860_);
v___x_865_ = v___x_799_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_r_795_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_927_; 
lean_inc(v_r_795_);
lean_inc(v_v_793_);
lean_inc(v_k_792_);
lean_inc(v_size_791_);
v_isSharedCheck_927_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; lean_object* v_unused_932_; 
v_unused_928_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_r_614_, 2);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_r_614_, 1);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_r_614_, 0);
lean_dec(v_unused_932_);
v___x_875_ = v_r_614_;
v_isShared_876_ = v_isSharedCheck_927_;
goto v_resetjp_874_;
}
else
{
lean_dec(v_r_614_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_927_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
if (lean_obj_tag(v_l_794_) == 0)
{
if (lean_obj_tag(v_r_795_) == 0)
{
lean_object* v_k_877_; lean_object* v_v_878_; lean_object* v_size_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v_k_877_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_k_877_);
v_v_878_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_v_878_);
lean_dec_ref(v___x_801_);
v_size_879_ = lean_ctor_get(v_l_794_, 0);
v___x_880_ = lean_nat_add(v___x_796_, v_size_791_);
lean_dec(v_size_791_);
v___x_881_ = lean_nat_add(v___x_796_, v_size_879_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_l_794_);
lean_ctor_set(v___x_875_, 3, v_tree_802_);
lean_ctor_set(v___x_875_, 2, v_v_878_);
lean_ctor_set(v___x_875_, 1, v_k_877_);
lean_ctor_set(v___x_875_, 0, v___x_881_);
v___x_883_ = v___x_875_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_tree_802_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_l_794_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_795_);
lean_ctor_set(v___x_799_, 3, v___x_883_);
lean_ctor_set(v___x_799_, 2, v_v_793_);
lean_ctor_set(v___x_799_, 1, v_k_792_);
lean_ctor_set(v___x_799_, 0, v___x_880_);
v___x_885_ = v___x_799_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_r_795_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v_k_888_; lean_object* v_v_889_; lean_object* v_k_890_; lean_object* v_v_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_size_791_);
v_k_888_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_k_888_);
v_v_889_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_v_889_);
lean_dec_ref(v___x_801_);
v_k_890_ = lean_ctor_get(v_l_794_, 1);
v_v_891_ = lean_ctor_get(v_l_794_, 2);
v_isSharedCheck_905_ = !lean_is_exclusive(v_l_794_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_906_ = lean_ctor_get(v_l_794_, 4);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_l_794_, 3);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_l_794_, 0);
lean_dec(v_unused_908_);
v___x_893_ = v_l_794_;
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_v_891_);
lean_inc(v_k_890_);
lean_dec(v_l_794_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_unsigned_to_nat(3u);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 4, v_r_795_);
lean_ctor_set(v___x_893_, 3, v_r_795_);
lean_ctor_set(v___x_893_, 2, v_v_889_);
lean_ctor_set(v___x_893_, 1, v_k_888_);
lean_ctor_set(v___x_893_, 0, v___x_796_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_888_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_889_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_r_795_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_795_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 3, v_r_795_);
lean_ctor_set(v___x_875_, 0, v___x_796_);
v___x_899_ = v___x_875_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_r_795_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_r_795_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v___x_899_);
lean_ctor_set(v___x_799_, 3, v___x_897_);
lean_ctor_set(v___x_799_, 2, v_v_891_);
lean_ctor_set(v___x_799_, 1, v_k_890_);
lean_ctor_set(v___x_799_, 0, v___x_895_);
v___x_901_ = v___x_799_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_795_) == 0)
{
lean_object* v_k_909_; lean_object* v_v_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec(v_size_791_);
v_k_909_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_k_909_);
v_v_910_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_v_910_);
lean_dec_ref(v___x_801_);
v___x_911_ = lean_unsigned_to_nat(3u);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_l_794_);
lean_ctor_set(v___x_875_, 2, v_v_910_);
lean_ctor_set(v___x_875_, 1, v_k_909_);
lean_ctor_set(v___x_875_, 0, v___x_796_);
v___x_913_ = v___x_875_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_909_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_910_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_l_794_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_l_794_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_795_);
lean_ctor_set(v___x_799_, 3, v___x_913_);
lean_ctor_set(v___x_799_, 2, v_v_793_);
lean_ctor_set(v___x_799_, 1, v_k_792_);
lean_ctor_set(v___x_799_, 0, v___x_911_);
v___x_915_ = v___x_799_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_r_795_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_k_918_; lean_object* v_v_919_; lean_object* v___x_921_; 
v_k_918_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_k_918_);
v_v_919_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_v_919_);
lean_dec_ref(v___x_801_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 3, v_r_795_);
v___x_921_ = v___x_875_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_size_791_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_r_795_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_r_795_);
v___x_921_ = v_reuseFailAlloc_926_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(2u);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v___x_921_);
lean_ctor_set(v___x_799_, 3, v_r_795_);
lean_ctor_set(v___x_799_, 2, v_v_919_);
lean_ctor_set(v___x_799_, 1, v_k_918_);
lean_ctor_set(v___x_799_, 0, v___x_922_);
v___x_924_ = v___x_799_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_918_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_v_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_r_795_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v___x_921_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
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
lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1091_; 
lean_inc(v_r_795_);
lean_inc(v_v_793_);
lean_inc(v_k_792_);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1092_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_r_614_, 2);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_r_614_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_r_614_, 0);
lean_dec(v_unused_1096_);
v___x_940_ = v_r_614_;
v_isShared_941_ = v_isSharedCheck_1091_;
goto v_resetjp_939_;
}
else
{
lean_dec(v_r_614_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1091_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v_tree_943_; 
v___x_942_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_792_, v_v_793_, v_l_794_, v_r_795_);
v_tree_943_ = lean_ctor_get(v___x_942_, 2);
lean_inc(v_tree_943_);
if (lean_obj_tag(v_tree_943_) == 0)
{
lean_object* v_k_944_; lean_object* v_v_945_; lean_object* v_size_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_k_944_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_k_944_);
v_v_945_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_v_945_);
lean_dec_ref(v___x_942_);
v_size_946_ = lean_ctor_get(v_tree_943_, 0);
v___x_947_ = lean_unsigned_to_nat(3u);
v___x_948_ = lean_nat_mul(v___x_947_, v_size_946_);
v___x_949_ = lean_nat_dec_lt(v___x_948_, v_size_786_);
lean_dec(v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_r_790_);
v___x_950_ = lean_nat_add(v___x_796_, v_size_786_);
v___x_951_ = lean_nat_add(v___x_950_, v_size_946_);
lean_dec(v___x_950_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_tree_943_);
lean_ctor_set(v___x_940_, 3, v_l_613_);
lean_ctor_set(v___x_940_, 2, v_v_945_);
lean_ctor_set(v___x_940_, 1, v_k_944_);
lean_ctor_set(v___x_940_, 0, v___x_951_);
v___x_953_ = v___x_940_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_l_613_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_tree_943_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1020_; 
lean_inc(v_l_789_);
lean_inc(v_v_788_);
lean_inc(v_k_787_);
lean_inc(v_size_786_);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; 
v_unused_1021_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_l_613_, 2);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_613_, 1);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_1025_);
v___x_956_ = v_l_613_;
v_isShared_957_ = v_isSharedCheck_1020_;
goto v_resetjp_955_;
}
else
{
lean_dec(v_l_613_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1020_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_size_958_; lean_object* v_size_959_; lean_object* v_k_960_; lean_object* v_v_961_; lean_object* v_l_962_; lean_object* v_r_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_size_958_ = lean_ctor_get(v_l_789_, 0);
v_size_959_ = lean_ctor_get(v_r_790_, 0);
v_k_960_ = lean_ctor_get(v_r_790_, 1);
v_v_961_ = lean_ctor_get(v_r_790_, 2);
v_l_962_ = lean_ctor_get(v_r_790_, 3);
v_r_963_ = lean_ctor_get(v_r_790_, 4);
v___x_964_ = lean_unsigned_to_nat(2u);
v___x_965_ = lean_nat_mul(v___x_964_, v_size_958_);
v___x_966_ = lean_nat_dec_lt(v_size_959_, v___x_965_);
lean_dec(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1004_; 
lean_inc(v_r_963_);
lean_inc(v_l_962_);
lean_inc(v_v_961_);
lean_inc(v_k_960_);
lean_del_object(v___x_956_);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_r_790_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; 
v_unused_1005_ = lean_ctor_get(v_r_790_, 4);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_r_790_, 3);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_r_790_, 2);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_r_790_, 1);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_r_790_, 0);
lean_dec(v_unused_1009_);
v___x_968_ = v_r_790_;
v_isShared_969_ = v_isSharedCheck_1004_;
goto v_resetjp_967_;
}
else
{
lean_dec(v_r_790_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1004_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___x_992_; lean_object* v___y_994_; 
v___x_970_ = lean_nat_add(v___x_796_, v_size_786_);
lean_dec(v_size_786_);
v___x_971_ = lean_nat_add(v___x_970_, v_size_946_);
lean_dec(v___x_970_);
v___x_992_ = lean_nat_add(v___x_796_, v_size_958_);
if (lean_obj_tag(v_l_962_) == 0)
{
lean_object* v_size_1002_; 
v_size_1002_ = lean_ctor_get(v_l_962_, 0);
lean_inc(v_size_1002_);
v___y_994_ = v_size_1002_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___y_994_ = v___x_1003_;
goto v___jp_993_;
}
v___jp_972_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_nat_add(v___y_973_, v___y_975_);
lean_dec(v___y_975_);
lean_dec(v___y_973_);
lean_inc_ref(v_tree_943_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 4, v_tree_943_);
lean_ctor_set(v___x_968_, 3, v_r_963_);
lean_ctor_set(v___x_968_, 2, v_v_945_);
lean_ctor_set(v___x_968_, 1, v_k_944_);
lean_ctor_set(v___x_968_, 0, v___x_976_);
v___x_978_ = v___x_968_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_r_963_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_tree_943_);
v___x_978_ = v_reuseFailAlloc_991_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_isSharedCheck_985_ = !lean_is_exclusive(v_tree_943_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_tree_943_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_tree_943_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_tree_943_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_tree_943_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_tree_943_, 0);
lean_dec(v_unused_990_);
v___x_980_ = v_tree_943_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_dec(v_tree_943_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 4, v___x_978_);
lean_ctor_set(v___x_980_, 3, v___y_974_);
lean_ctor_set(v___x_980_, 2, v_v_961_);
lean_ctor_set(v___x_980_, 1, v_k_960_);
lean_ctor_set(v___x_980_, 0, v___x_971_);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_960_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_961_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v___y_974_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v___x_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_nat_add(v___x_992_, v___y_994_);
lean_dec(v___y_994_);
lean_dec(v___x_992_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_l_962_);
lean_ctor_set(v___x_940_, 3, v_l_789_);
lean_ctor_set(v___x_940_, 2, v_v_788_);
lean_ctor_set(v___x_940_, 1, v_k_787_);
lean_ctor_set(v___x_940_, 0, v___x_995_);
v___x_997_ = v___x_940_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_l_789_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_l_962_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; 
v___x_998_ = lean_nat_add(v___x_796_, v_size_946_);
if (lean_obj_tag(v_r_963_) == 0)
{
lean_object* v_size_999_; 
v_size_999_ = lean_ctor_get(v_r_963_, 0);
lean_inc(v_size_999_);
v___y_973_ = v___x_998_;
v___y_974_ = v___x_997_;
v___y_975_ = v_size_999_;
goto v___jp_972_;
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___y_973_ = v___x_998_;
v___y_974_ = v___x_997_;
v___y_975_ = v___x_1000_;
goto v___jp_972_;
}
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1010_ = lean_nat_add(v___x_796_, v_size_786_);
lean_dec(v_size_786_);
v___x_1011_ = lean_nat_add(v___x_1010_, v_size_946_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_nat_add(v___x_796_, v_size_946_);
v___x_1013_ = lean_nat_add(v___x_1012_, v_size_959_);
lean_dec(v___x_1012_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_tree_943_);
lean_ctor_set(v___x_940_, 3, v_r_790_);
lean_ctor_set(v___x_940_, 2, v_v_945_);
lean_ctor_set(v___x_940_, 1, v_k_944_);
lean_ctor_set(v___x_940_, 0, v___x_1013_);
v___x_1015_ = v___x_940_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_r_790_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_tree_943_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 4, v___x_1015_);
lean_ctor_set(v___x_956_, 0, v___x_1011_);
v___x_1017_ = v___x_956_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_l_789_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_789_) == 0)
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1049_; 
lean_inc_ref(v_l_789_);
lean_inc(v_v_788_);
lean_inc(v_k_787_);
lean_inc(v_size_786_);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; lean_object* v_unused_1054_; 
v_unused_1050_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_l_613_, 2);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_l_613_, 1);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_1054_);
v___x_1027_ = v_l_613_;
v_isShared_1028_ = v_isSharedCheck_1049_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v_l_613_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1049_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_r_790_) == 0)
{
lean_object* v_k_1029_; lean_object* v_v_1030_; lean_object* v_size_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v_k_1029_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_k_1029_);
v_v_1030_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_v_1030_);
lean_dec_ref(v___x_942_);
v_size_1031_ = lean_ctor_get(v_r_790_, 0);
v___x_1032_ = lean_nat_add(v___x_796_, v_size_786_);
lean_dec(v_size_786_);
v___x_1033_ = lean_nat_add(v___x_796_, v_size_1031_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_tree_943_);
lean_ctor_set(v___x_940_, 3, v_r_790_);
lean_ctor_set(v___x_940_, 2, v_v_1030_);
lean_ctor_set(v___x_940_, 1, v_k_1029_);
lean_ctor_set(v___x_940_, 0, v___x_1033_);
v___x_1035_ = v___x_940_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_1030_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_r_790_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_tree_943_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 4, v___x_1035_);
lean_ctor_set(v___x_1027_, 0, v___x_1032_);
v___x_1037_ = v___x_1027_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_l_789_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_k_1040_; lean_object* v_v_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v_size_786_);
v_k_1040_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_k_1040_);
v_v_1041_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_v_1041_);
lean_dec_ref(v___x_942_);
v___x_1042_ = lean_unsigned_to_nat(3u);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_r_790_);
lean_ctor_set(v___x_940_, 3, v_r_790_);
lean_ctor_set(v___x_940_, 2, v_v_1041_);
lean_ctor_set(v___x_940_, 1, v_k_1040_);
lean_ctor_set(v___x_940_, 0, v___x_796_);
v___x_1044_ = v___x_940_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_1040_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_1041_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_r_790_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_r_790_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 4, v___x_1044_);
lean_ctor_set(v___x_1027_, 0, v___x_1042_);
v___x_1046_ = v___x_1027_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_l_789_);
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
}
}
else
{
if (lean_obj_tag(v_r_790_) == 0)
{
lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1079_; 
lean_inc(v_l_789_);
lean_inc(v_v_788_);
lean_inc(v_k_787_);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_l_613_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; lean_object* v_unused_1081_; lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; 
v_unused_1080_ = lean_ctor_get(v_l_613_, 4);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_l_613_, 3);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_l_613_, 2);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_613_, 1);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_613_, 0);
lean_dec(v_unused_1084_);
v___x_1056_ = v_l_613_;
v_isShared_1057_ = v_isSharedCheck_1079_;
goto v_resetjp_1055_;
}
else
{
lean_dec(v_l_613_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1079_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_k_1058_; lean_object* v_v_1059_; lean_object* v_k_1060_; lean_object* v_v_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1075_; 
v_k_1058_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_k_1058_);
v_v_1059_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_v_1059_);
lean_dec_ref(v___x_942_);
v_k_1060_ = lean_ctor_get(v_r_790_, 1);
v_v_1061_ = lean_ctor_get(v_r_790_, 2);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_r_790_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1076_ = lean_ctor_get(v_r_790_, 4);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_r_790_, 3);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_r_790_, 0);
lean_dec(v_unused_1078_);
v___x_1063_ = v_r_790_;
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_v_1061_);
lean_inc(v_k_1060_);
lean_dec(v_r_790_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_unsigned_to_nat(3u);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 4, v_l_789_);
lean_ctor_set(v___x_1063_, 3, v_l_789_);
lean_ctor_set(v___x_1063_, 2, v_v_788_);
lean_ctor_set(v___x_1063_, 1, v_k_787_);
lean_ctor_set(v___x_1063_, 0, v___x_796_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_l_789_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_l_789_);
v___x_1067_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_l_789_);
lean_ctor_set(v___x_940_, 3, v_l_789_);
lean_ctor_set(v___x_940_, 2, v_v_1059_);
lean_ctor_set(v___x_940_, 1, v_k_1058_);
lean_ctor_set(v___x_940_, 0, v___x_796_);
v___x_1069_ = v___x_940_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1058_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1059_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_l_789_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_l_789_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___x_1069_);
lean_ctor_set(v___x_1056_, 3, v___x_1067_);
lean_ctor_set(v___x_1056_, 2, v_v_1061_);
lean_ctor_set(v___x_1056_, 1, v_k_1060_);
lean_ctor_set(v___x_1056_, 0, v___x_1065_);
v___x_1071_ = v___x_1056_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
else
{
lean_object* v_k_1085_; lean_object* v_v_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v_k_1085_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_k_1085_);
v_v_1086_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_v_1086_);
lean_dec_ref(v___x_942_);
v___x_1087_ = lean_unsigned_to_nat(2u);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_r_790_);
lean_ctor_set(v___x_940_, 3, v_l_613_);
lean_ctor_set(v___x_940_, 2, v_v_1086_);
lean_ctor_set(v___x_940_, 1, v_k_1085_);
lean_ctor_set(v___x_940_, 0, v___x_1087_);
v___x_1089_ = v___x_940_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_l_613_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_r_790_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
}
else
{
return v_l_613_;
}
}
else
{
return v_r_614_;
}
}
}
else
{
lean_object* v_impl_1097_; lean_object* v___x_1098_; 
v_impl_1097_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_609_, v_l_613_);
v___x_1098_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1097_) == 0)
{
if (lean_obj_tag(v_r_614_) == 0)
{
lean_object* v_size_1099_; lean_object* v_size_1100_; lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v_l_1103_; lean_object* v_r_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_size_1099_ = lean_ctor_get(v_impl_1097_, 0);
lean_inc(v_size_1099_);
v_size_1100_ = lean_ctor_get(v_r_614_, 0);
v_k_1101_ = lean_ctor_get(v_r_614_, 1);
v_v_1102_ = lean_ctor_get(v_r_614_, 2);
v_l_1103_ = lean_ctor_get(v_r_614_, 3);
lean_inc(v_l_1103_);
v_r_1104_ = lean_ctor_get(v_r_614_, 4);
v___x_1105_ = lean_unsigned_to_nat(3u);
v___x_1106_ = lean_nat_mul(v___x_1105_, v_size_1099_);
v___x_1107_ = lean_nat_dec_lt(v___x_1106_, v_size_1100_);
lean_dec(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec(v_l_1103_);
v___x_1108_ = lean_nat_add(v___x_1098_, v_size_1099_);
lean_dec(v_size_1099_);
v___x_1109_ = lean_nat_add(v___x_1108_, v_size_1100_);
lean_dec(v___x_1108_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 3, v_impl_1097_);
lean_ctor_set(v___x_616_, 0, v___x_1109_);
v___x_1111_ = v___x_616_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_614_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1176_; 
lean_inc(v_r_1104_);
lean_inc(v_v_1102_);
lean_inc(v_k_1101_);
lean_inc(v_size_1100_);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1177_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_r_614_, 2);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_r_614_, 1);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_r_614_, 0);
lean_dec(v_unused_1181_);
v___x_1114_ = v_r_614_;
v_isShared_1115_ = v_isSharedCheck_1176_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v_r_614_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1176_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_size_1116_; lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v_l_1119_; lean_object* v_r_1120_; lean_object* v_size_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_size_1116_ = lean_ctor_get(v_l_1103_, 0);
v_k_1117_ = lean_ctor_get(v_l_1103_, 1);
v_v_1118_ = lean_ctor_get(v_l_1103_, 2);
v_l_1119_ = lean_ctor_get(v_l_1103_, 3);
v_r_1120_ = lean_ctor_get(v_l_1103_, 4);
v_size_1121_ = lean_ctor_get(v_r_1104_, 0);
v___x_1122_ = lean_unsigned_to_nat(2u);
v___x_1123_ = lean_nat_mul(v___x_1122_, v_size_1121_);
v___x_1124_ = lean_nat_dec_lt(v_size_1116_, v___x_1123_);
lean_dec(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1152_; 
lean_inc(v_r_1120_);
lean_inc(v_l_1119_);
lean_inc(v_v_1118_);
lean_inc(v_k_1117_);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_l_1103_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; 
v_unused_1153_ = lean_ctor_get(v_l_1103_, 4);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_l_1103_, 3);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_l_1103_, 2);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_l_1103_, 1);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_l_1103_, 0);
lean_dec(v_unused_1157_);
v___x_1126_ = v_l_1103_;
v_isShared_1127_ = v_isSharedCheck_1152_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_l_1103_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1152_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1142_; 
v___x_1128_ = lean_nat_add(v___x_1098_, v_size_1099_);
lean_dec(v_size_1099_);
v___x_1129_ = lean_nat_add(v___x_1128_, v_size_1100_);
lean_dec(v_size_1100_);
if (lean_obj_tag(v_l_1119_) == 0)
{
lean_object* v_size_1150_; 
v_size_1150_ = lean_ctor_get(v_l_1119_, 0);
lean_inc(v_size_1150_);
v___y_1142_ = v_size_1150_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v___y_1142_ = v___x_1151_;
goto v___jp_1141_;
}
v___jp_1130_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_nat_add(v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec(v___y_1132_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1104_);
lean_ctor_set(v___x_1126_, 3, v_r_1120_);
lean_ctor_set(v___x_1126_, 2, v_v_1102_);
lean_ctor_set(v___x_1126_, 1, v_k_1101_);
lean_ctor_set(v___x_1126_, 0, v___x_1134_);
v___x_1136_ = v___x_1126_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_r_1120_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_r_1104_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1136_);
lean_ctor_set(v___x_1114_, 3, v___y_1131_);
lean_ctor_set(v___x_1114_, 2, v_v_1118_);
lean_ctor_set(v___x_1114_, 1, v_k_1117_);
lean_ctor_set(v___x_1114_, 0, v___x_1129_);
v___x_1138_ = v___x_1114_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1117_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1118_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___y_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_nat_add(v___x_1128_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v___x_1128_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_l_1119_);
lean_ctor_set(v___x_616_, 3, v_impl_1097_);
lean_ctor_set(v___x_616_, 0, v___x_1143_);
v___x_1145_ = v___x_616_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_l_1119_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_nat_add(v___x_1098_, v_size_1121_);
if (lean_obj_tag(v_r_1120_) == 0)
{
lean_object* v_size_1147_; 
v_size_1147_ = lean_ctor_get(v_r_1120_, 0);
lean_inc(v_size_1147_);
v___y_1131_ = v___x_1145_;
v___y_1132_ = v___x_1146_;
v___y_1133_ = v_size_1147_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___y_1131_ = v___x_1145_;
v___y_1132_ = v___x_1146_;
v___y_1133_ = v___x_1148_;
goto v___jp_1130_;
}
}
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_del_object(v___x_616_);
v___x_1158_ = lean_nat_add(v___x_1098_, v_size_1099_);
lean_dec(v_size_1099_);
v___x_1159_ = lean_nat_add(v___x_1158_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1160_ = lean_nat_add(v___x_1158_, v_size_1116_);
lean_dec(v___x_1158_);
lean_inc_ref(v_impl_1097_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_l_1103_);
lean_ctor_set(v___x_1114_, 3, v_impl_1097_);
lean_ctor_set(v___x_1114_, 2, v_v_612_);
lean_ctor_set(v___x_1114_, 1, v_k_611_);
lean_ctor_set(v___x_1114_, 0, v___x_1160_);
v___x_1162_ = v___x_1114_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_l_1103_);
v___x_1162_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_isSharedCheck_1169_ = !lean_is_exclusive(v_impl_1097_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1170_ = lean_ctor_get(v_impl_1097_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_impl_1097_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_impl_1097_, 2);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_impl_1097_, 1);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_impl_1097_, 0);
lean_dec(v_unused_1174_);
v___x_1164_ = v_impl_1097_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v_impl_1097_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 4, v_r_1104_);
lean_ctor_set(v___x_1164_, 3, v___x_1162_);
lean_ctor_set(v___x_1164_, 2, v_v_1102_);
lean_ctor_set(v___x_1164_, 1, v_k_1101_);
lean_ctor_set(v___x_1164_, 0, v___x_1159_);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_r_1104_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v_size_1182_ = lean_ctor_get(v_impl_1097_, 0);
lean_inc(v_size_1182_);
v___x_1183_ = lean_nat_add(v___x_1098_, v_size_1182_);
lean_dec(v_size_1182_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 3, v_impl_1097_);
lean_ctor_set(v___x_616_, 0, v___x_1183_);
v___x_1185_ = v___x_616_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_r_614_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
if (lean_obj_tag(v_r_614_) == 0)
{
lean_object* v_l_1187_; 
v_l_1187_ = lean_ctor_get(v_r_614_, 3);
lean_inc(v_l_1187_);
if (lean_obj_tag(v_l_1187_) == 0)
{
lean_object* v_r_1188_; 
v_r_1188_ = lean_ctor_get(v_r_614_, 4);
lean_inc(v_r_1188_);
if (lean_obj_tag(v_r_1188_) == 0)
{
lean_object* v_size_1189_; lean_object* v_k_1190_; lean_object* v_v_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1204_; 
v_size_1189_ = lean_ctor_get(v_r_614_, 0);
v_k_1190_ = lean_ctor_get(v_r_614_, 1);
v_v_1191_ = lean_ctor_get(v_r_614_, 2);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; lean_object* v_unused_1206_; 
v_unused_1205_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_1206_);
v___x_1193_ = v_r_614_;
v_isShared_1194_ = v_isSharedCheck_1204_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_v_1191_);
lean_inc(v_k_1190_);
lean_inc(v_size_1189_);
lean_dec(v_r_614_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1204_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_size_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v_size_1195_ = lean_ctor_get(v_l_1187_, 0);
v___x_1196_ = lean_nat_add(v___x_1098_, v_size_1189_);
lean_dec(v_size_1189_);
v___x_1197_ = lean_nat_add(v___x_1098_, v_size_1195_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 4, v_l_1187_);
lean_ctor_set(v___x_1193_, 3, v_impl_1097_);
lean_ctor_set(v___x_1193_, 2, v_v_612_);
lean_ctor_set(v___x_1193_, 1, v_k_611_);
lean_ctor_set(v___x_1193_, 0, v___x_1197_);
v___x_1199_ = v___x_1193_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_l_1187_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_r_1188_);
lean_ctor_set(v___x_616_, 3, v___x_1199_);
lean_ctor_set(v___x_616_, 2, v_v_1191_);
lean_ctor_set(v___x_616_, 1, v_k_1190_);
lean_ctor_set(v___x_616_, 0, v___x_1196_);
v___x_1201_ = v___x_616_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1191_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_r_1188_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_k_1207_; lean_object* v_v_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1231_; 
v_k_1207_ = lean_ctor_get(v_r_614_, 1);
v_v_1208_ = lean_ctor_get(v_r_614_, 2);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; lean_object* v_unused_1233_; lean_object* v_unused_1234_; 
v_unused_1232_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_r_614_, 0);
lean_dec(v_unused_1234_);
v___x_1210_ = v_r_614_;
v_isShared_1211_ = v_isSharedCheck_1231_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_v_1208_);
lean_inc(v_k_1207_);
lean_dec(v_r_614_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1231_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_k_1212_; lean_object* v_v_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1227_; 
v_k_1212_ = lean_ctor_get(v_l_1187_, 1);
v_v_1213_ = lean_ctor_get(v_l_1187_, 2);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_l_1187_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; lean_object* v_unused_1229_; lean_object* v_unused_1230_; 
v_unused_1228_ = lean_ctor_get(v_l_1187_, 4);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_l_1187_, 3);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_l_1187_, 0);
lean_dec(v_unused_1230_);
v___x_1215_ = v_l_1187_;
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_v_1213_);
lean_inc(v_k_1212_);
lean_dec(v_l_1187_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(3u);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 4, v_r_1188_);
lean_ctor_set(v___x_1215_, 3, v_r_1188_);
lean_ctor_set(v___x_1215_, 2, v_v_612_);
lean_ctor_set(v___x_1215_, 1, v_k_611_);
lean_ctor_set(v___x_1215_, 0, v___x_1098_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_r_1188_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_r_1188_);
v___x_1219_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 3, v_r_1188_);
lean_ctor_set(v___x_1210_, 0, v___x_1098_);
v___x_1221_ = v___x_1210_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_1207_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_1208_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_r_1188_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_r_1188_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_1221_);
lean_ctor_set(v___x_616_, 3, v___x_1219_);
lean_ctor_set(v___x_616_, 2, v_v_1213_);
lean_ctor_set(v___x_616_, 1, v_k_1212_);
lean_ctor_set(v___x_616_, 0, v___x_1217_);
v___x_1223_ = v___x_616_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_k_1212_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_v_1213_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1235_; 
v_r_1235_ = lean_ctor_get(v_r_614_, 4);
lean_inc(v_r_1235_);
if (lean_obj_tag(v_r_1235_) == 0)
{
lean_object* v_k_1236_; lean_object* v_v_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1248_; 
v_k_1236_ = lean_ctor_get(v_r_614_, 1);
v_v_1237_ = lean_ctor_get(v_r_614_, 2);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1249_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_r_614_, 0);
lean_dec(v_unused_1251_);
v___x_1239_ = v_r_614_;
v_isShared_1240_ = v_isSharedCheck_1248_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_v_1237_);
lean_inc(v_k_1236_);
lean_dec(v_r_614_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1248_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(3u);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 4, v_l_1187_);
lean_ctor_set(v___x_1239_, 2, v_v_612_);
lean_ctor_set(v___x_1239_, 1, v_k_611_);
lean_ctor_set(v___x_1239_, 0, v___x_1098_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_l_1187_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_l_1187_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v_r_1235_);
lean_ctor_set(v___x_616_, 3, v___x_1243_);
lean_ctor_set(v___x_616_, 2, v_v_1237_);
lean_ctor_set(v___x_616_, 1, v_k_1236_);
lean_ctor_set(v___x_616_, 0, v___x_1241_);
v___x_1245_ = v___x_616_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1237_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_r_1235_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_size_1252_; lean_object* v_k_1253_; lean_object* v_v_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1265_; 
v_size_1252_ = lean_ctor_get(v_r_614_, 0);
v_k_1253_ = lean_ctor_get(v_r_614_, 1);
v_v_1254_ = lean_ctor_get(v_r_614_, 2);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_r_614_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; lean_object* v_unused_1267_; 
v_unused_1266_ = lean_ctor_get(v_r_614_, 4);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v_r_614_, 3);
lean_dec(v_unused_1267_);
v___x_1256_ = v_r_614_;
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_v_1254_);
lean_inc(v_k_1253_);
lean_inc(v_size_1252_);
lean_dec(v_r_614_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 3, v_r_1235_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_size_1252_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_k_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_v_1254_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_r_1235_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_r_1235_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(2u);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_1259_);
lean_ctor_set(v___x_616_, 3, v_r_1235_);
lean_ctor_set(v___x_616_, 0, v___x_1260_);
v___x_1262_ = v___x_616_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_r_1235_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v___x_1259_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
else
{
lean_object* v___x_1269_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 3, v_r_614_);
lean_ctor_set(v___x_616_, 0, v___x_1098_);
v___x_1269_ = v___x_616_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_r_614_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_r_614_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
}
else
{
return v_t_610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg___boxed(lean_object* v_k_1273_, lean_object* v_t_1274_){
_start:
{
uint64_t v_k_boxed_1275_; lean_object* v_res_1276_; 
v_k_boxed_1275_ = lean_unbox_uint64(v_k_1273_);
lean_dec_ref(v_k_1273_);
v_res_1276_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_boxed_1275_, v_t_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t v_h_1277_, lean_object* v_st_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_h_1277_, v_st_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object* v_h_1280_, lean_object* v_st_1281_){
_start:
{
uint64_t v_h_boxed_1282_; lean_object* v_res_1283_; 
v_h_boxed_1282_ = lean_unbox_uint64(v_h_1280_);
lean_dec_ref(v_h_1280_);
v_res_1283_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_1282_, v_st_1281_);
return v_res_1283_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_ctor_set(v___x_1290_, 2, v___x_1289_);
lean_ctor_set(v___x_1290_, 3, v___x_1289_);
lean_ctor_set(v___x_1290_, 4, v___x_1289_);
lean_ctor_set(v___x_1290_, 5, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_env_1296_; lean_object* v_nextMacroScope_1297_; lean_object* v_ngen_1298_; lean_object* v_auxDeclNGen_1299_; lean_object* v_traceState_1300_; lean_object* v_messages_1301_; lean_object* v_infoState_1302_; lean_object* v_snapshotTasks_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1333_; 
v___x_1295_ = lean_st_ref_take(v___y_1293_);
v_env_1296_ = lean_ctor_get(v___x_1295_, 0);
v_nextMacroScope_1297_ = lean_ctor_get(v___x_1295_, 1);
v_ngen_1298_ = lean_ctor_get(v___x_1295_, 2);
v_auxDeclNGen_1299_ = lean_ctor_get(v___x_1295_, 3);
v_traceState_1300_ = lean_ctor_get(v___x_1295_, 4);
v_messages_1301_ = lean_ctor_get(v___x_1295_, 6);
v_infoState_1302_ = lean_ctor_get(v___x_1295_, 7);
v_snapshotTasks_1303_ = lean_ctor_get(v___x_1295_, 8);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v___x_1295_, 5);
lean_dec(v_unused_1334_);
v___x_1305_ = v___x_1295_;
v_isShared_1306_ = v_isSharedCheck_1333_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snapshotTasks_1303_);
lean_inc(v_infoState_1302_);
lean_inc(v_messages_1301_);
lean_inc(v_traceState_1300_);
lean_inc(v_auxDeclNGen_1299_);
lean_inc(v_ngen_1298_);
lean_inc(v_nextMacroScope_1297_);
lean_inc(v_env_1296_);
lean_dec(v___x_1295_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1333_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1307_ = lean_box_uint64(v_h_1291_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1308_, 0, v___x_1307_);
v___x_1309_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1310_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1309_, v_env_1296_, v___f_1308_);
v___x_1311_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 5, v___x_1311_);
lean_ctor_set(v___x_1305_, 0, v___x_1310_);
v___x_1313_ = v___x_1305_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_nextMacroScope_1297_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_ngen_1298_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_auxDeclNGen_1299_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_traceState_1300_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1332_, 6, v_messages_1301_);
lean_ctor_set(v_reuseFailAlloc_1332_, 7, v_infoState_1302_);
lean_ctor_set(v_reuseFailAlloc_1332_, 8, v_snapshotTasks_1303_);
v___x_1313_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_mctx_1316_; lean_object* v_zetaDeltaFVarIds_1317_; lean_object* v_postponed_1318_; lean_object* v_diag_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1330_; 
v___x_1314_ = lean_st_ref_put(v___y_1293_, v___x_1313_);
v___x_1315_ = lean_st_ref_take(v___y_1292_);
v_mctx_1316_ = lean_ctor_get(v___x_1315_, 0);
v_zetaDeltaFVarIds_1317_ = lean_ctor_get(v___x_1315_, 2);
v_postponed_1318_ = lean_ctor_get(v___x_1315_, 3);
v_diag_1319_ = lean_ctor_get(v___x_1315_, 4);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v___x_1315_, 1);
lean_dec(v_unused_1331_);
v___x_1321_ = v___x_1315_;
v_isShared_1322_ = v_isSharedCheck_1330_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_diag_1319_);
lean_inc(v_postponed_1318_);
lean_inc(v_zetaDeltaFVarIds_1317_);
lean_inc(v_mctx_1316_);
lean_dec(v___x_1315_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1330_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_mctx_1316_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_zetaDeltaFVarIds_1317_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v_postponed_1318_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v_diag_1319_);
v___x_1325_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_st_ref_put(v___y_1292_, v___x_1325_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint64_t v_h_boxed_1339_; lean_object* v_res_1340_; 
v_h_boxed_1339_ = lean_unbox_uint64(v_h_1335_);
lean_dec_ref(v_h_1335_);
v_res_1340_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1339_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1341_, uint64_t v_k_1342_, lean_object* v_fallback_1343_){
_start:
{
if (lean_obj_tag(v_t_1341_) == 0)
{
lean_object* v_k_1344_; lean_object* v_v_1345_; lean_object* v_l_1346_; lean_object* v_r_1347_; uint64_t v___x_1348_; uint8_t v___x_1349_; 
v_k_1344_ = lean_ctor_get(v_t_1341_, 1);
v_v_1345_ = lean_ctor_get(v_t_1341_, 2);
v_l_1346_ = lean_ctor_get(v_t_1341_, 3);
v_r_1347_ = lean_ctor_get(v_t_1341_, 4);
v___x_1348_ = lean_unbox_uint64(v_k_1344_);
v___x_1349_ = lean_uint64_dec_lt(v_k_1342_, v___x_1348_);
if (v___x_1349_ == 0)
{
uint64_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = lean_unbox_uint64(v_k_1344_);
v___x_1351_ = lean_uint64_dec_eq(v_k_1342_, v___x_1350_);
if (v___x_1351_ == 0)
{
v_t_1341_ = v_r_1347_;
goto _start;
}
else
{
lean_inc(v_v_1345_);
return v_v_1345_;
}
}
else
{
v_t_1341_ = v_l_1346_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1343_);
return v_fallback_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1354_, lean_object* v_k_1355_, lean_object* v_fallback_1356_){
_start:
{
uint64_t v_k_boxed_1357_; lean_object* v_res_1358_; 
v_k_boxed_1357_ = lean_unbox_uint64(v_k_1355_);
lean_dec_ref(v_k_1355_);
v_res_1358_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1354_, v_k_boxed_1357_, v_fallback_1356_);
lean_dec(v_fallback_1356_);
lean_dec(v_t_1354_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1359_, lean_object* v_v_1360_, lean_object* v_t_1361_){
_start:
{
if (lean_obj_tag(v_t_1361_) == 0)
{
lean_object* v_size_1362_; lean_object* v_k_1363_; lean_object* v_v_1364_; lean_object* v_l_1365_; lean_object* v_r_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1650_; 
v_size_1362_ = lean_ctor_get(v_t_1361_, 0);
v_k_1363_ = lean_ctor_get(v_t_1361_, 1);
v_v_1364_ = lean_ctor_get(v_t_1361_, 2);
v_l_1365_ = lean_ctor_get(v_t_1361_, 3);
v_r_1366_ = lean_ctor_get(v_t_1361_, 4);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_t_1361_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1368_ = v_t_1361_;
v_isShared_1369_ = v_isSharedCheck_1650_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_r_1366_);
lean_inc(v_l_1365_);
lean_inc(v_v_1364_);
lean_inc(v_k_1363_);
lean_inc(v_size_1362_);
lean_dec(v_t_1361_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1650_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint64_t v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_unbox_uint64(v_k_1363_);
v___x_1371_ = lean_uint64_dec_lt(v_k_1359_, v___x_1370_);
if (v___x_1371_ == 0)
{
uint64_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_unbox_uint64(v_k_1363_);
v___x_1373_ = lean_uint64_dec_eq(v_k_1359_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v_impl_1374_; lean_object* v___x_1375_; 
lean_dec(v_size_1362_);
v_impl_1374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1359_, v_v_1360_, v_r_1366_);
v___x_1375_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1365_) == 0)
{
lean_object* v_size_1376_; lean_object* v_size_1377_; lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v_l_1380_; lean_object* v_r_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_size_1376_ = lean_ctor_get(v_l_1365_, 0);
v_size_1377_ = lean_ctor_get(v_impl_1374_, 0);
lean_inc(v_size_1377_);
v_k_1378_ = lean_ctor_get(v_impl_1374_, 1);
lean_inc(v_k_1378_);
v_v_1379_ = lean_ctor_get(v_impl_1374_, 2);
lean_inc(v_v_1379_);
v_l_1380_ = lean_ctor_get(v_impl_1374_, 3);
lean_inc(v_l_1380_);
v_r_1381_ = lean_ctor_get(v_impl_1374_, 4);
lean_inc(v_r_1381_);
v___x_1382_ = lean_unsigned_to_nat(3u);
v___x_1383_ = lean_nat_mul(v___x_1382_, v_size_1376_);
v___x_1384_ = lean_nat_dec_lt(v___x_1383_, v_size_1377_);
lean_dec(v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_dec(v_r_1381_);
lean_dec(v_l_1380_);
lean_dec(v_v_1379_);
lean_dec(v_k_1378_);
v___x_1385_ = lean_nat_add(v___x_1375_, v_size_1376_);
v___x_1386_ = lean_nat_add(v___x_1385_, v_size_1377_);
lean_dec(v_size_1377_);
lean_dec(v___x_1385_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_impl_1374_);
lean_ctor_set(v___x_1368_, 0, v___x_1386_);
v___x_1388_ = v___x_1368_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_l_1365_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_impl_1374_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1453_; 
v_isSharedCheck_1453_ = !lean_is_exclusive(v_impl_1374_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1454_ = lean_ctor_get(v_impl_1374_, 4);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_impl_1374_, 3);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_impl_1374_, 2);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_impl_1374_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_impl_1374_, 0);
lean_dec(v_unused_1458_);
v___x_1391_ = v_impl_1374_;
v_isShared_1392_ = v_isSharedCheck_1453_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v_impl_1374_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1453_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_size_1393_; lean_object* v_k_1394_; lean_object* v_v_1395_; lean_object* v_l_1396_; lean_object* v_r_1397_; lean_object* v_size_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_size_1393_ = lean_ctor_get(v_l_1380_, 0);
v_k_1394_ = lean_ctor_get(v_l_1380_, 1);
v_v_1395_ = lean_ctor_get(v_l_1380_, 2);
v_l_1396_ = lean_ctor_get(v_l_1380_, 3);
v_r_1397_ = lean_ctor_get(v_l_1380_, 4);
v_size_1398_ = lean_ctor_get(v_r_1381_, 0);
v___x_1399_ = lean_unsigned_to_nat(2u);
v___x_1400_ = lean_nat_mul(v___x_1399_, v_size_1398_);
v___x_1401_ = lean_nat_dec_lt(v_size_1393_, v___x_1400_);
lean_dec(v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1429_; 
lean_inc(v_r_1397_);
lean_inc(v_l_1396_);
lean_inc(v_v_1395_);
lean_inc(v_k_1394_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; 
v_unused_1430_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1434_);
v___x_1403_ = v_l_1380_;
v_isShared_1404_ = v_isSharedCheck_1429_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v_l_1380_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1429_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1419_; 
v___x_1405_ = lean_nat_add(v___x_1375_, v_size_1376_);
v___x_1406_ = lean_nat_add(v___x_1405_, v_size_1377_);
lean_dec(v_size_1377_);
if (lean_obj_tag(v_l_1396_) == 0)
{
lean_object* v_size_1427_; 
v_size_1427_ = lean_ctor_get(v_l_1396_, 0);
lean_inc(v_size_1427_);
v___y_1419_ = v_size_1427_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___y_1419_ = v___x_1428_;
goto v___jp_1418_;
}
v___jp_1407_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_nat_add(v___y_1408_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec(v___y_1408_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_r_1381_);
lean_ctor_set(v___x_1403_, 3, v_r_1397_);
lean_ctor_set(v___x_1403_, 2, v_v_1379_);
lean_ctor_set(v___x_1403_, 1, v_k_1378_);
lean_ctor_set(v___x_1403_, 0, v___x_1411_);
v___x_1413_ = v___x_1403_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_r_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_r_1381_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v___x_1413_);
lean_ctor_set(v___x_1391_, 3, v___y_1409_);
lean_ctor_set(v___x_1391_, 2, v_v_1395_);
lean_ctor_set(v___x_1391_, 1, v_k_1394_);
lean_ctor_set(v___x_1391_, 0, v___x_1406_);
v___x_1415_ = v___x_1391_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1394_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1395_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___y_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
v___jp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_nat_add(v___x_1405_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec(v___x_1405_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_l_1396_);
lean_ctor_set(v___x_1368_, 0, v___x_1420_);
v___x_1422_ = v___x_1368_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_l_1365_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_l_1396_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_nat_add(v___x_1375_, v_size_1398_);
if (lean_obj_tag(v_r_1397_) == 0)
{
lean_object* v_size_1424_; 
v_size_1424_ = lean_ctor_get(v_r_1397_, 0);
lean_inc(v_size_1424_);
v___y_1408_ = v___x_1423_;
v___y_1409_ = v___x_1422_;
v___y_1410_ = v_size_1424_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v___y_1408_ = v___x_1423_;
v___y_1409_ = v___x_1422_;
v___y_1410_ = v___x_1425_;
goto v___jp_1407_;
}
}
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_del_object(v___x_1368_);
v___x_1435_ = lean_nat_add(v___x_1375_, v_size_1376_);
v___x_1436_ = lean_nat_add(v___x_1435_, v_size_1377_);
lean_dec(v_size_1377_);
v___x_1437_ = lean_nat_add(v___x_1435_, v_size_1393_);
lean_dec(v___x_1435_);
lean_inc_ref(v_l_1365_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_l_1380_);
lean_ctor_set(v___x_1391_, 3, v_l_1365_);
lean_ctor_set(v___x_1391_, 2, v_v_1364_);
lean_ctor_set(v___x_1391_, 1, v_k_1363_);
lean_ctor_set(v___x_1391_, 0, v___x_1437_);
v___x_1439_ = v___x_1391_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_l_1365_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_l_1380_);
v___x_1439_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_isSharedCheck_1446_ = !lean_is_exclusive(v_l_1365_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; 
v_unused_1447_ = lean_ctor_get(v_l_1365_, 4);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_l_1365_, 3);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1365_, 2);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_l_1365_, 1);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1365_, 0);
lean_dec(v_unused_1451_);
v___x_1441_ = v_l_1365_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_l_1365_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_r_1381_);
lean_ctor_set(v___x_1441_, 3, v___x_1439_);
lean_ctor_set(v___x_1441_, 2, v_v_1379_);
lean_ctor_set(v___x_1441_, 1, v_k_1378_);
lean_ctor_set(v___x_1441_, 0, v___x_1436_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1381_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1459_; 
v_l_1459_ = lean_ctor_get(v_impl_1374_, 3);
lean_inc(v_l_1459_);
if (lean_obj_tag(v_l_1459_) == 0)
{
lean_object* v_r_1460_; lean_object* v_k_1461_; lean_object* v_v_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1485_; 
v_r_1460_ = lean_ctor_get(v_impl_1374_, 4);
v_k_1461_ = lean_ctor_get(v_impl_1374_, 1);
v_v_1462_ = lean_ctor_get(v_impl_1374_, 2);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_impl_1374_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; lean_object* v_unused_1487_; 
v_unused_1486_ = lean_ctor_get(v_impl_1374_, 3);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_impl_1374_, 0);
lean_dec(v_unused_1487_);
v___x_1464_ = v_impl_1374_;
v_isShared_1465_ = v_isSharedCheck_1485_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_r_1460_);
lean_inc(v_v_1462_);
lean_inc(v_k_1461_);
lean_dec(v_impl_1374_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1485_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1481_; 
v_k_1466_ = lean_ctor_get(v_l_1459_, 1);
v_v_1467_ = lean_ctor_get(v_l_1459_, 2);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_l_1459_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1482_ = lean_ctor_get(v_l_1459_, 4);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_l_1459_, 3);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1459_, 0);
lean_dec(v_unused_1484_);
v___x_1469_ = v_l_1459_;
v_isShared_1470_ = v_isSharedCheck_1481_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
lean_dec(v_l_1459_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1481_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1460_, 2);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 4, v_r_1460_);
lean_ctor_set(v___x_1469_, 3, v_r_1460_);
lean_ctor_set(v___x_1469_, 2, v_v_1364_);
lean_ctor_set(v___x_1469_, 1, v_k_1363_);
lean_ctor_set(v___x_1469_, 0, v___x_1375_);
v___x_1473_ = v___x_1469_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1460_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1460_);
v___x_1473_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
lean_inc(v_r_1460_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 3, v_r_1460_);
lean_ctor_set(v___x_1464_, 0, v___x_1375_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1461_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1462_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1460_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1460_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v___x_1475_);
lean_ctor_set(v___x_1368_, 3, v___x_1473_);
lean_ctor_set(v___x_1368_, 2, v_v_1467_);
lean_ctor_set(v___x_1368_, 1, v_k_1466_);
lean_ctor_set(v___x_1368_, 0, v___x_1471_);
v___x_1477_ = v___x_1368_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
else
{
lean_object* v_r_1488_; 
v_r_1488_ = lean_ctor_get(v_impl_1374_, 4);
lean_inc(v_r_1488_);
if (lean_obj_tag(v_r_1488_) == 0)
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1501_; 
v_k_1489_ = lean_ctor_get(v_impl_1374_, 1);
v_v_1490_ = lean_ctor_get(v_impl_1374_, 2);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_impl_1374_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1502_ = lean_ctor_get(v_impl_1374_, 4);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_impl_1374_, 3);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_impl_1374_, 0);
lean_dec(v_unused_1504_);
v___x_1492_ = v_impl_1374_;
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_dec(v_impl_1374_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(3u);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 4, v_l_1459_);
lean_ctor_set(v___x_1492_, 2, v_v_1364_);
lean_ctor_set(v___x_1492_, 1, v_k_1363_);
lean_ctor_set(v___x_1492_, 0, v___x_1375_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1459_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1459_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_r_1488_);
lean_ctor_set(v___x_1368_, 3, v___x_1496_);
lean_ctor_set(v___x_1368_, 2, v_v_1490_);
lean_ctor_set(v___x_1368_, 1, v_k_1489_);
lean_ctor_set(v___x_1368_, 0, v___x_1494_);
v___x_1498_ = v___x_1368_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1488_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(2u);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_impl_1374_);
lean_ctor_set(v___x_1368_, 3, v_r_1488_);
lean_ctor_set(v___x_1368_, 0, v___x_1505_);
v___x_1507_ = v___x_1368_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1488_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_impl_1374_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_dec(v_v_1364_);
lean_dec(v_k_1363_);
v___x_1509_ = lean_box_uint64(v_k_1359_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 2, v_v_1360_);
lean_ctor_set(v___x_1368_, 1, v___x_1509_);
v___x_1511_ = v___x_1368_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_size_1362_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_l_1365_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_r_1366_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v_impl_1513_; lean_object* v___x_1514_; 
lean_dec(v_size_1362_);
v_impl_1513_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1359_, v_v_1360_, v_l_1365_);
v___x_1514_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1366_) == 0)
{
lean_object* v_size_1515_; lean_object* v_size_1516_; lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v_l_1519_; lean_object* v_r_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_size_1515_ = lean_ctor_get(v_r_1366_, 0);
v_size_1516_ = lean_ctor_get(v_impl_1513_, 0);
lean_inc(v_size_1516_);
v_k_1517_ = lean_ctor_get(v_impl_1513_, 1);
lean_inc(v_k_1517_);
v_v_1518_ = lean_ctor_get(v_impl_1513_, 2);
lean_inc(v_v_1518_);
v_l_1519_ = lean_ctor_get(v_impl_1513_, 3);
lean_inc(v_l_1519_);
v_r_1520_ = lean_ctor_get(v_impl_1513_, 4);
lean_inc(v_r_1520_);
v___x_1521_ = lean_unsigned_to_nat(3u);
v___x_1522_ = lean_nat_mul(v___x_1521_, v_size_1515_);
v___x_1523_ = lean_nat_dec_lt(v___x_1522_, v_size_1516_);
lean_dec(v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_dec(v_r_1520_);
lean_dec(v_l_1519_);
lean_dec(v_v_1518_);
lean_dec(v_k_1517_);
v___x_1524_ = lean_nat_add(v___x_1514_, v_size_1516_);
lean_dec(v_size_1516_);
v___x_1525_ = lean_nat_add(v___x_1524_, v_size_1515_);
lean_dec(v___x_1524_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 3, v_impl_1513_);
lean_ctor_set(v___x_1368_, 0, v___x_1525_);
v___x_1527_ = v___x_1368_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_impl_1513_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1366_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1594_; 
v_isSharedCheck_1594_ = !lean_is_exclusive(v_impl_1513_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1595_ = lean_ctor_get(v_impl_1513_, 4);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_impl_1513_, 3);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_impl_1513_, 2);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1513_, 1);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1513_, 0);
lean_dec(v_unused_1599_);
v___x_1530_ = v_impl_1513_;
v_isShared_1531_ = v_isSharedCheck_1594_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_impl_1513_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1594_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_size_1532_; lean_object* v_size_1533_; lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v_l_1536_; lean_object* v_r_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_size_1532_ = lean_ctor_get(v_l_1519_, 0);
v_size_1533_ = lean_ctor_get(v_r_1520_, 0);
v_k_1534_ = lean_ctor_get(v_r_1520_, 1);
v_v_1535_ = lean_ctor_get(v_r_1520_, 2);
v_l_1536_ = lean_ctor_get(v_r_1520_, 3);
v_r_1537_ = lean_ctor_get(v_r_1520_, 4);
v___x_1538_ = lean_unsigned_to_nat(2u);
v___x_1539_ = lean_nat_mul(v___x_1538_, v_size_1532_);
v___x_1540_ = lean_nat_dec_lt(v_size_1533_, v___x_1539_);
lean_dec(v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1569_; 
lean_inc(v_r_1537_);
lean_inc(v_l_1536_);
lean_inc(v_v_1535_);
lean_inc(v_k_1534_);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_r_1520_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; lean_object* v_unused_1571_; lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; 
v_unused_1570_ = lean_ctor_get(v_r_1520_, 4);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_r_1520_, 3);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_r_1520_, 2);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_r_1520_, 1);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_r_1520_, 0);
lean_dec(v_unused_1574_);
v___x_1542_ = v_r_1520_;
v_isShared_1543_ = v_isSharedCheck_1569_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v_r_1520_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1569_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___x_1557_; lean_object* v___y_1559_; 
v___x_1544_ = lean_nat_add(v___x_1514_, v_size_1516_);
lean_dec(v_size_1516_);
v___x_1545_ = lean_nat_add(v___x_1544_, v_size_1515_);
lean_dec(v___x_1544_);
v___x_1557_ = lean_nat_add(v___x_1514_, v_size_1532_);
if (lean_obj_tag(v_l_1536_) == 0)
{
lean_object* v_size_1567_; 
v_size_1567_ = lean_ctor_get(v_l_1536_, 0);
lean_inc(v_size_1567_);
v___y_1559_ = v_size_1567_;
goto v___jp_1558_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___y_1559_ = v___x_1568_;
goto v___jp_1558_;
}
v___jp_1546_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_nat_add(v___y_1547_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec(v___y_1547_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 4, v_r_1366_);
lean_ctor_set(v___x_1542_, 3, v_r_1537_);
lean_ctor_set(v___x_1542_, 2, v_v_1364_);
lean_ctor_set(v___x_1542_, 1, v_k_1363_);
lean_ctor_set(v___x_1542_, 0, v___x_1550_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_r_1537_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_r_1366_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 4, v___x_1552_);
lean_ctor_set(v___x_1530_, 3, v___y_1548_);
lean_ctor_set(v___x_1530_, 2, v_v_1535_);
lean_ctor_set(v___x_1530_, 1, v_k_1534_);
lean_ctor_set(v___x_1530_, 0, v___x_1545_);
v___x_1554_ = v___x_1530_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_1534_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_v_1535_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v___y_1548_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
v___jp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = lean_nat_add(v___x_1557_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec(v___x_1557_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_l_1536_);
lean_ctor_set(v___x_1368_, 3, v_l_1519_);
lean_ctor_set(v___x_1368_, 2, v_v_1518_);
lean_ctor_set(v___x_1368_, 1, v_k_1517_);
lean_ctor_set(v___x_1368_, 0, v___x_1560_);
v___x_1562_ = v___x_1368_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1517_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1518_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_l_1519_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v_l_1536_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_nat_add(v___x_1514_, v_size_1515_);
if (lean_obj_tag(v_r_1537_) == 0)
{
lean_object* v_size_1564_; 
v_size_1564_ = lean_ctor_get(v_r_1537_, 0);
lean_inc(v_size_1564_);
v___y_1547_ = v___x_1563_;
v___y_1548_ = v___x_1562_;
v___y_1549_ = v_size_1564_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_unsigned_to_nat(0u);
v___y_1547_ = v___x_1563_;
v___y_1548_ = v___x_1562_;
v___y_1549_ = v___x_1565_;
goto v___jp_1546_;
}
}
}
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_del_object(v___x_1368_);
v___x_1575_ = lean_nat_add(v___x_1514_, v_size_1516_);
lean_dec(v_size_1516_);
v___x_1576_ = lean_nat_add(v___x_1575_, v_size_1515_);
lean_dec(v___x_1575_);
v___x_1577_ = lean_nat_add(v___x_1514_, v_size_1515_);
v___x_1578_ = lean_nat_add(v___x_1577_, v_size_1533_);
lean_dec(v___x_1577_);
lean_inc_ref(v_r_1366_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 4, v_r_1366_);
lean_ctor_set(v___x_1530_, 3, v_r_1520_);
lean_ctor_set(v___x_1530_, 2, v_v_1364_);
lean_ctor_set(v___x_1530_, 1, v_k_1363_);
lean_ctor_set(v___x_1530_, 0, v___x_1578_);
v___x_1580_ = v___x_1530_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_r_1520_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_r_1366_);
v___x_1580_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v_r_1366_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1588_ = lean_ctor_get(v_r_1366_, 4);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_r_1366_, 3);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_r_1366_, 2);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_r_1366_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_r_1366_, 0);
lean_dec(v_unused_1592_);
v___x_1582_ = v_r_1366_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_r_1366_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v___x_1580_);
lean_ctor_set(v___x_1582_, 3, v_l_1519_);
lean_ctor_set(v___x_1582_, 2, v_v_1518_);
lean_ctor_set(v___x_1582_, 1, v_k_1517_);
lean_ctor_set(v___x_1582_, 0, v___x_1576_);
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1517_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1518_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_l_1519_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v___x_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1600_; 
v_l_1600_ = lean_ctor_get(v_impl_1513_, 3);
lean_inc(v_l_1600_);
if (lean_obj_tag(v_l_1600_) == 0)
{
lean_object* v_r_1601_; lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1614_; 
v_r_1601_ = lean_ctor_get(v_impl_1513_, 4);
v_k_1602_ = lean_ctor_get(v_impl_1513_, 1);
v_v_1603_ = lean_ctor_get(v_impl_1513_, 2);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_impl_1513_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1615_ = lean_ctor_get(v_impl_1513_, 3);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1513_, 0);
lean_dec(v_unused_1616_);
v___x_1605_ = v_impl_1513_;
v_isShared_1606_ = v_isSharedCheck_1614_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_r_1601_);
lean_inc(v_v_1603_);
lean_inc(v_k_1602_);
lean_dec(v_impl_1513_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1614_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1601_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v_r_1601_);
lean_ctor_set(v___x_1605_, 2, v_v_1364_);
lean_ctor_set(v___x_1605_, 1, v_k_1363_);
lean_ctor_set(v___x_1605_, 0, v___x_1514_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_r_1601_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_r_1601_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v___x_1609_);
lean_ctor_set(v___x_1368_, 3, v_l_1600_);
lean_ctor_set(v___x_1368_, 2, v_v_1603_);
lean_ctor_set(v___x_1368_, 1, v_k_1602_);
lean_ctor_set(v___x_1368_, 0, v___x_1607_);
v___x_1611_ = v___x_1368_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_k_1602_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_v_1603_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_l_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_r_1617_; 
v_r_1617_ = lean_ctor_get(v_impl_1513_, 4);
lean_inc(v_r_1617_);
if (lean_obj_tag(v_r_1617_) == 0)
{
lean_object* v_k_1618_; lean_object* v_v_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1642_; 
v_k_1618_ = lean_ctor_get(v_impl_1513_, 1);
v_v_1619_ = lean_ctor_get(v_impl_1513_, 2);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_impl_1513_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1643_ = lean_ctor_get(v_impl_1513_, 4);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_impl_1513_, 3);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_impl_1513_, 0);
lean_dec(v_unused_1645_);
v___x_1621_ = v_impl_1513_;
v_isShared_1622_ = v_isSharedCheck_1642_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_v_1619_);
lean_inc(v_k_1618_);
lean_dec(v_impl_1513_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1642_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_k_1623_; lean_object* v_v_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1638_; 
v_k_1623_ = lean_ctor_get(v_r_1617_, 1);
v_v_1624_ = lean_ctor_get(v_r_1617_, 2);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_r_1617_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; 
v_unused_1639_ = lean_ctor_get(v_r_1617_, 4);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_r_1617_, 3);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_r_1617_, 0);
lean_dec(v_unused_1641_);
v___x_1626_ = v_r_1617_;
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_v_1624_);
lean_inc(v_k_1623_);
lean_dec(v_r_1617_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(3u);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 4, v_l_1600_);
lean_ctor_set(v___x_1626_, 3, v_l_1600_);
lean_ctor_set(v___x_1626_, 2, v_v_1619_);
lean_ctor_set(v___x_1626_, 1, v_k_1618_);
lean_ctor_set(v___x_1626_, 0, v___x_1514_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1618_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1619_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_l_1600_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_l_1600_);
v___x_1630_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 4, v_l_1600_);
lean_ctor_set(v___x_1621_, 2, v_v_1364_);
lean_ctor_set(v___x_1621_, 1, v_k_1363_);
lean_ctor_set(v___x_1621_, 0, v___x_1514_);
v___x_1632_ = v___x_1621_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_l_1600_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_l_1600_);
v___x_1632_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1634_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v___x_1632_);
lean_ctor_set(v___x_1368_, 3, v___x_1630_);
lean_ctor_set(v___x_1368_, 2, v_v_1624_);
lean_ctor_set(v___x_1368_, 1, v_k_1623_);
lean_ctor_set(v___x_1368_, 0, v___x_1628_);
v___x_1634_ = v___x_1368_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1623_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1624_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(2u);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_r_1617_);
lean_ctor_set(v___x_1368_, 3, v_impl_1513_);
lean_ctor_set(v___x_1368_, 0, v___x_1646_);
v___x_1648_ = v___x_1368_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_impl_1513_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_r_1617_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_box_uint64(v_k_1359_);
v___x_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
lean_ctor_set(v___x_1653_, 2, v_v_1360_);
lean_ctor_set(v___x_1653_, 3, v_t_1361_);
lean_ctor_set(v___x_1653_, 4, v_t_1361_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1654_, lean_object* v_v_1655_, lean_object* v_t_1656_){
_start:
{
uint64_t v_k_boxed_1657_; lean_object* v_res_1658_; 
v_k_boxed_1657_ = lean_unbox_uint64(v_k_1654_);
lean_dec_ref(v_k_1654_);
v_res_1658_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1657_, v_v_1655_, v_t_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1659_, lean_object* v_s_1660_){
_start:
{
uint64_t v_javascriptHash_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_javascriptHash_1661_ = lean_ctor_get_uint64(v_wi_1659_, sizeof(void*)*2);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_wi_1659_);
v___x_1663_ = lean_box(0);
v___x_1664_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1660_, v_javascriptHash_1661_, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1662_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1661_, v___x_1665_, v_s_1660_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v_env_1672_; lean_object* v_nextMacroScope_1673_; lean_object* v_ngen_1674_; lean_object* v_auxDeclNGen_1675_; lean_object* v_traceState_1676_; lean_object* v_messages_1677_; lean_object* v_infoState_1678_; lean_object* v_snapshotTasks_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1708_; 
v___x_1671_ = lean_st_ref_take(v___y_1669_);
v_env_1672_ = lean_ctor_get(v___x_1671_, 0);
v_nextMacroScope_1673_ = lean_ctor_get(v___x_1671_, 1);
v_ngen_1674_ = lean_ctor_get(v___x_1671_, 2);
v_auxDeclNGen_1675_ = lean_ctor_get(v___x_1671_, 3);
v_traceState_1676_ = lean_ctor_get(v___x_1671_, 4);
v_messages_1677_ = lean_ctor_get(v___x_1671_, 6);
v_infoState_1678_ = lean_ctor_get(v___x_1671_, 7);
v_snapshotTasks_1679_ = lean_ctor_get(v___x_1671_, 8);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1671_, 5);
lean_dec(v_unused_1709_);
v___x_1681_ = v___x_1671_;
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snapshotTasks_1679_);
lean_inc(v_infoState_1678_);
lean_inc(v_messages_1677_);
lean_inc(v_traceState_1676_);
lean_inc(v_auxDeclNGen_1675_);
lean_inc(v_ngen_1674_);
lean_inc(v_nextMacroScope_1673_);
lean_inc(v_env_1672_);
lean_dec(v___x_1671_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___f_1683_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1683_, 0, v_wi_1667_);
v___x_1684_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1685_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1684_, v_env_1672_, v___f_1683_);
v___x_1686_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 5, v___x_1686_);
lean_ctor_set(v___x_1681_, 0, v___x_1685_);
v___x_1688_ = v___x_1681_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_nextMacroScope_1673_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_ngen_1674_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_auxDeclNGen_1675_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_traceState_1676_);
lean_ctor_set(v_reuseFailAlloc_1707_, 5, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_messages_1677_);
lean_ctor_set(v_reuseFailAlloc_1707_, 7, v_infoState_1678_);
lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_snapshotTasks_1679_);
v___x_1688_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v_mctx_1691_; lean_object* v_zetaDeltaFVarIds_1692_; lean_object* v_postponed_1693_; lean_object* v_diag_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1705_; 
v___x_1689_ = lean_st_ref_put(v___y_1669_, v___x_1688_);
v___x_1690_ = lean_st_ref_take(v___y_1668_);
v_mctx_1691_ = lean_ctor_get(v___x_1690_, 0);
v_zetaDeltaFVarIds_1692_ = lean_ctor_get(v___x_1690_, 2);
v_postponed_1693_ = lean_ctor_get(v___x_1690_, 3);
v_diag_1694_ = lean_ctor_get(v___x_1690_, 4);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v___x_1690_, 1);
lean_dec(v_unused_1706_);
v___x_1696_ = v___x_1690_;
v_isShared_1697_ = v_isSharedCheck_1705_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_diag_1694_);
lean_inc(v_postponed_1693_);
lean_inc(v_zetaDeltaFVarIds_1692_);
lean_inc(v_mctx_1691_);
lean_dec(v___x_1690_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1705_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_mctx_1691_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_zetaDeltaFVarIds_1692_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_postponed_1693_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_diag_1694_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_st_ref_put(v___y_1668_, v___x_1700_);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
return v___x_1703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(lean_object* v_ext_1715_, lean_object* v_b_1716_, uint8_t v_kind_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_currNamespace_1722_; lean_object* v___x_1723_; lean_object* v_env_1724_; lean_object* v_nextMacroScope_1725_; lean_object* v_ngen_1726_; lean_object* v_auxDeclNGen_1727_; lean_object* v_traceState_1728_; lean_object* v_messages_1729_; lean_object* v_infoState_1730_; lean_object* v_snapshotTasks_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1758_; 
v_currNamespace_1722_ = lean_ctor_get(v___y_1719_, 6);
v___x_1723_ = lean_st_ref_take(v___y_1720_);
v_env_1724_ = lean_ctor_get(v___x_1723_, 0);
v_nextMacroScope_1725_ = lean_ctor_get(v___x_1723_, 1);
v_ngen_1726_ = lean_ctor_get(v___x_1723_, 2);
v_auxDeclNGen_1727_ = lean_ctor_get(v___x_1723_, 3);
v_traceState_1728_ = lean_ctor_get(v___x_1723_, 4);
v_messages_1729_ = lean_ctor_get(v___x_1723_, 6);
v_infoState_1730_ = lean_ctor_get(v___x_1723_, 7);
v_snapshotTasks_1731_ = lean_ctor_get(v___x_1723_, 8);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v___x_1723_, 5);
lean_dec(v_unused_1759_);
v___x_1733_ = v___x_1723_;
v_isShared_1734_ = v_isSharedCheck_1758_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_snapshotTasks_1731_);
lean_inc(v_infoState_1730_);
lean_inc(v_messages_1729_);
lean_inc(v_traceState_1728_);
lean_inc(v_auxDeclNGen_1727_);
lean_inc(v_ngen_1726_);
lean_inc(v_nextMacroScope_1725_);
lean_inc(v_env_1724_);
lean_dec(v___x_1723_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1758_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_inc(v_currNamespace_1722_);
v___x_1735_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1724_, v_ext_1715_, v_b_1716_, v_kind_1717_, v_currNamespace_1722_);
v___x_1736_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 5, v___x_1736_);
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1738_ = v___x_1733_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_nextMacroScope_1725_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_ngen_1726_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_auxDeclNGen_1727_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_traceState_1728_);
lean_ctor_set(v_reuseFailAlloc_1757_, 5, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1757_, 6, v_messages_1729_);
lean_ctor_set(v_reuseFailAlloc_1757_, 7, v_infoState_1730_);
lean_ctor_set(v_reuseFailAlloc_1757_, 8, v_snapshotTasks_1731_);
v___x_1738_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_mctx_1741_; lean_object* v_zetaDeltaFVarIds_1742_; lean_object* v_postponed_1743_; lean_object* v_diag_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1755_; 
v___x_1739_ = lean_st_ref_put(v___y_1720_, v___x_1738_);
v___x_1740_ = lean_st_ref_take(v___y_1718_);
v_mctx_1741_ = lean_ctor_get(v___x_1740_, 0);
v_zetaDeltaFVarIds_1742_ = lean_ctor_get(v___x_1740_, 2);
v_postponed_1743_ = lean_ctor_get(v___x_1740_, 3);
v_diag_1744_ = lean_ctor_get(v___x_1740_, 4);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v___x_1740_, 1);
lean_dec(v_unused_1756_);
v___x_1746_ = v___x_1740_;
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_diag_1744_);
lean_inc(v_postponed_1743_);
lean_inc(v_zetaDeltaFVarIds_1742_);
lean_inc(v_mctx_1741_);
lean_dec(v___x_1740_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_mctx_1741_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_zetaDeltaFVarIds_1742_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_postponed_1743_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_diag_1744_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_st_ref_put(v___y_1718_, v___x_1750_);
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(lean_object* v_ext_1760_, lean_object* v_b_1761_, lean_object* v_kind_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v_kind_boxed_1767_; lean_object* v_res_1768_; 
v_kind_boxed_1767_ = lean_unbox(v_kind_1762_);
v_res_1768_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_1760_, v_b_1761_, v_kind_boxed_1767_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1769_, lean_object* v_n_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1778_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1779_ = lean_box_uint64(v_h_1769_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v_n_1770_);
v___x_1781_ = 0;
v___x_1782_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1778_, v___x_1780_, v___x_1781_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1783_, lean_object* v_n_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint64_t v_h_boxed_1792_; lean_object* v_res_1793_; 
v_h_boxed_1792_ = lean_unbox_uint64(v_h_1783_);
lean_dec_ref(v_h_1783_);
v_res_1793_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1792_, v_n_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1794_, lean_object* v_declName_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint8_t v___x_1798_; lean_object* v_env_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1798_ = 0;
v_env_1799_ = l_Lean_Environment_setExporting(v_env_1794_, v___x_1798_);
lean_inc(v_declName_1795_);
v___x_1800_ = l_Lean_mkPrivateName(v_env_1799_, v_declName_1795_);
v___x_1801_ = 1;
lean_inc_ref(v_env_1799_);
v___x_1802_ = l_Lean_Environment_contains(v_env_1799_, v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = l_Lean_privateToUserName(v_declName_1795_);
v___x_1804_ = l_Lean_Environment_contains(v_env_1799_, v___x_1803_, v___x_1801_);
v___x_1805_ = lean_box(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___y_1797_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declName_1795_);
v___x_1807_ = lean_box(v___x_1802_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___y_1797_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1809_, lean_object* v_declName_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1809_, v_declName_1810_, v___y_1811_, v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_env_1814_, lean_object* v_currNamespace_1815_, lean_object* v_openDecls_1816_, lean_object* v_n_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Lean_ResolveName_resolveNamespace(v_env_1814_, v_currNamespace_1815_, v_openDecls_1816_, v_n_1817_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___y_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_env_1822_, lean_object* v_currNamespace_1823_, lean_object* v_openDecls_1824_, lean_object* v_n_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_env_1822_, v_currNamespace_1823_, v_openDecls_1824_, v_n_1825_, v___y_1826_, v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(lean_object* v_msgData_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; lean_object* v_env_1836_; lean_object* v___x_1837_; lean_object* v_mctx_1838_; lean_object* v_lctx_1839_; lean_object* v_options_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1835_ = lean_st_ref_get(v___y_1833_);
v_env_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_env_1836_);
lean_dec(v___x_1835_);
v___x_1837_ = lean_st_ref_get(v___y_1831_);
v_mctx_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref(v_mctx_1838_);
lean_dec(v___x_1837_);
v_lctx_1839_ = lean_ctor_get(v___y_1830_, 2);
v_options_1840_ = lean_ctor_get(v___y_1832_, 2);
lean_inc_ref(v_options_1840_);
lean_inc_ref(v_lctx_1839_);
v___x_1841_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1841_, 0, v_env_1836_);
lean_ctor_set(v___x_1841_, 1, v_mctx_1838_);
lean_ctor_set(v___x_1841_, 2, v_lctx_1839_);
lean_ctor_set(v___x_1841_, 3, v_options_1840_);
v___x_1842_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_msgData_1829_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object* v_msgData_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1850_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1851_; double v___x_1852_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_float_of_nat(v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_ref_1862_; lean_object* v___x_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1908_; 
v_ref_1862_ = lean_ctor_get(v___y_1859_, 5);
v___x_1863_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1908_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1908_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v_traceState_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_cache_1874_; lean_object* v_messages_1875_; lean_object* v_infoState_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1907_; 
v___x_1868_ = lean_st_ref_take(v___y_1860_);
v_traceState_1869_ = lean_ctor_get(v___x_1868_, 4);
v_env_1870_ = lean_ctor_get(v___x_1868_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1868_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1868_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1868_, 3);
v_cache_1874_ = lean_ctor_get(v___x_1868_, 5);
v_messages_1875_ = lean_ctor_get(v___x_1868_, 6);
v_infoState_1876_ = lean_ctor_get(v___x_1868_, 7);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1868_, 8);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1879_ = v___x_1868_;
v_isShared_1880_ = v_isSharedCheck_1907_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1876_);
lean_inc(v_messages_1875_);
lean_inc(v_cache_1874_);
lean_inc(v_traceState_1869_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1907_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
uint64_t v_tid_1881_; lean_object* v_traces_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1906_; 
v_tid_1881_ = lean_ctor_get_uint64(v_traceState_1869_, sizeof(void*)*1);
v_traces_1882_ = lean_ctor_get(v_traceState_1869_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_traceState_1869_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1884_ = v_traceState_1869_;
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_traces_1882_);
lean_dec(v_traceState_1869_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; double v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1888_ = 0;
v___x_1889_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1890_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1890_, 0, v_cls_1855_);
lean_ctor_set(v___x_1890_, 1, v___x_1886_);
lean_ctor_set(v___x_1890_, 2, v___x_1889_);
lean_ctor_set_float(v___x_1890_, sizeof(void*)*3, v___x_1887_);
lean_ctor_set_float(v___x_1890_, sizeof(void*)*3 + 8, v___x_1887_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*3 + 16, v___x_1888_);
v___x_1891_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1892_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v_a_1864_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
lean_inc(v_ref_1862_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_ref_1862_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_PersistentArray_push___redArg(v_traces_1882_, v___x_1893_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1894_);
v___x_1896_ = v___x_1884_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1894_);
lean_ctor_set_uint64(v_reuseFailAlloc_1905_, sizeof(void*)*1, v_tid_1881_);
v___x_1896_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 4, v___x_1896_);
v___x_1898_ = v___x_1879_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_env_1870_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1904_, 4, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1904_, 5, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1904_, 6, v_messages_1875_);
lean_ctor_set(v_reuseFailAlloc_1904_, 7, v_infoState_1876_);
lean_ctor_set(v_reuseFailAlloc_1904_, 8, v_snapshotTasks_1877_);
v___x_1898_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1899_ = lean_st_ref_put(v___y_1860_, v___x_1898_);
v___x_1900_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1900_);
v___x_1902_ = v___x_1866_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1909_, lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1909_, v_msg_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
if (lean_obj_tag(v_as_1920_) == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
else
{
lean_object* v_options_1930_; uint8_t v_hasTrace_1931_; 
v_options_1930_ = lean_ctor_get(v___y_1925_, 2);
v_hasTrace_1931_ = lean_ctor_get_uint8(v_options_1930_, sizeof(void*)*1);
if (v_hasTrace_1931_ == 0)
{
lean_object* v_tail_1932_; 
v_tail_1932_ = lean_ctor_get(v_as_1920_, 1);
lean_inc(v_tail_1932_);
lean_dec_ref_known(v_as_1920_, 2);
v_as_1920_ = v_tail_1932_;
goto _start;
}
else
{
lean_object* v_head_1934_; lean_object* v_tail_1935_; lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v_inheritedTraceOptions_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_head_1934_ = lean_ctor_get(v_as_1920_, 0);
lean_inc(v_head_1934_);
v_tail_1935_ = lean_ctor_get(v_as_1920_, 1);
lean_inc(v_tail_1935_);
lean_dec_ref_known(v_as_1920_, 2);
v_fst_1936_ = lean_ctor_get(v_head_1934_, 0);
lean_inc_n(v_fst_1936_, 2);
v_snd_1937_ = lean_ctor_get(v_head_1934_, 1);
lean_inc(v_snd_1937_);
lean_dec(v_head_1934_);
v_inheritedTraceOptions_1938_ = lean_ctor_get(v___y_1925_, 13);
v___x_1939_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_1940_ = l_Lean_Name_append(v___x_1939_, v_fst_1936_);
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1938_, v_options_1930_, v___x_1940_);
lean_dec(v___x_1940_);
if (v___x_1941_ == 0)
{
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
v_as_1920_ = v_tail_1935_;
goto _start;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_snd_1937_);
v___x_1944_ = l_Lean_MessageData_ofFormat(v___x_1943_);
v___x_1945_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_1936_, v___x_1944_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_dec_ref_known(v___x_1945_, 1);
v_as_1920_ = v_tail_1935_;
goto _start;
}
else
{
lean_dec(v_tail_1935_);
return v___x_1945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1955_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object* v_opts_1956_, lean_object* v_opt_1957_){
_start:
{
lean_object* v_name_1958_; lean_object* v_defValue_1959_; lean_object* v_map_1960_; lean_object* v___x_1961_; 
v_name_1958_ = lean_ctor_get(v_opt_1957_, 0);
v_defValue_1959_ = lean_ctor_get(v_opt_1957_, 1);
v_map_1960_ = lean_ctor_get(v_opts_1956_, 0);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1960_, v_name_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_unbox(v_defValue_1959_);
return v___x_1962_;
}
else
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v___x_1961_, 1);
if (lean_obj_tag(v_val_1963_) == 1)
{
uint8_t v_v_1964_; 
v_v_1964_ = lean_ctor_get_uint8(v_val_1963_, 0);
lean_dec_ref_known(v_val_1963_, 0);
return v_v_1964_;
}
else
{
uint8_t v___x_1965_; 
lean_dec(v_val_1963_);
v___x_1965_ = lean_unbox(v_defValue_1959_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object* v_opts_1966_, lean_object* v_opt_1967_){
_start:
{
uint8_t v_res_1968_; lean_object* v_r_1969_; 
v_res_1968_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_1966_, v_opt_1967_);
lean_dec_ref(v_opt_1967_);
lean_dec_ref(v_opts_1966_);
v_r_1969_ = lean_box(v_res_1968_);
return v_r_1969_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_box(1);
v___x_1971_ = l_Lean_MessageData_ofFormat(v___x_1970_);
return v___x_1971_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2));
v___x_1976_ = l_Lean_MessageData_ofFormat(v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
if (lean_obj_tag(v_x_1978_) == 0)
{
return v_x_1977_;
}
else
{
lean_object* v_head_1979_; lean_object* v_tail_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2002_; 
v_head_1979_ = lean_ctor_get(v_x_1978_, 0);
v_tail_1980_ = lean_ctor_get(v_x_1978_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1982_ = v_x_1978_;
v_isShared_1983_ = v_isSharedCheck_2002_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_tail_1980_);
lean_inc(v_head_1979_);
lean_dec(v_x_1978_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2002_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_before_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2000_; 
v_before_1984_ = lean_ctor_get(v_head_1979_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_head_1979_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_head_1979_, 1);
lean_dec(v_unused_2001_);
v___x_1986_ = v_head_1979_;
v_isShared_1987_ = v_isSharedCheck_2000_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_before_1984_);
lean_dec(v_head_1979_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2000_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 7);
lean_ctor_set(v___x_1986_, 1, v___x_1988_);
lean_ctor_set(v___x_1986_, 0, v_x_1977_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_x_1977_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 7);
lean_ctor_set(v___x_1982_, 1, v___x_1991_);
lean_ctor_set(v___x_1982_, 0, v___x_1990_);
v___x_1993_ = v___x_1982_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_MessageData_ofSyntax(v_before_1984_);
v___x_1995_ = l_Lean_indentD(v___x_1994_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1993_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v_x_1977_ = v___x_1996_;
v_x_1978_ = v_tail_1980_;
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
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1));
v___x_2007_ = l_Lean_MessageData_ofFormat(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object* v_msgData_2008_, lean_object* v_macroStack_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_options_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_options_2012_ = lean_ctor_get(v___y_2010_, 2);
v___x_2013_ = l_Lean_Elab_pp_macroStack;
v___x_2014_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_options_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec(v_macroStack_2009_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_msgData_2008_);
return v___x_2015_;
}
else
{
if (lean_obj_tag(v_macroStack_2009_) == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_msgData_2008_);
return v___x_2016_;
}
else
{
lean_object* v_head_2017_; lean_object* v_after_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2033_; 
v_head_2017_ = lean_ctor_get(v_macroStack_2009_, 0);
lean_inc(v_head_2017_);
v_after_2018_ = lean_ctor_get(v_head_2017_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_head_2017_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v_head_2017_, 0);
lean_dec(v_unused_2034_);
v___x_2020_ = v_head_2017_;
v_isShared_2021_ = v_isSharedCheck_2033_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_after_2018_);
lean_dec(v_head_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2033_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 7);
lean_ctor_set(v___x_2020_, 1, v___x_2022_);
lean_ctor_set(v___x_2020_, 0, v_msgData_2008_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_msgData_2008_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v_msgData_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2025_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = l_Lean_MessageData_ofSyntax(v_after_2018_);
v___x_2028_ = l_Lean_indentD(v___x_2027_);
v_msgData_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2029_, 0, v___x_2026_);
lean_ctor_set(v_msgData_2029_, 1, v___x_2028_);
v___x_2030_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_2029_, v_macroStack_2009_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object* v_msgData_2035_, lean_object* v_macroStack_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2035_, v_macroStack_2036_, v___y_2037_);
lean_dec_ref(v___y_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_ref_2048_; lean_object* v___x_2049_; lean_object* v_a_2050_; lean_object* v_macroStack_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2062_; 
v_ref_2048_ = lean_ctor_get(v___y_2045_, 5);
v___x_2049_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_2040_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v_macroStack_2051_ = lean_ctor_get(v___y_2041_, 1);
v___x_2052_ = l_Lean_Elab_getBetterRef(v_ref_2048_, v_macroStack_2051_);
lean_inc(v_macroStack_2051_);
v___x_2053_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_2050_, v_macroStack_2051_, v___y_2045_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2052_);
lean_ctor_set(v___x_2058_, 1, v_a_2054_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 1);
lean_ctor_set(v___x_2056_, 0, v___x_2058_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2072_, lean_object* v_msg_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_fileName_2081_; lean_object* v_fileMap_2082_; lean_object* v_options_2083_; lean_object* v_currRecDepth_2084_; lean_object* v_maxRecDepth_2085_; lean_object* v_ref_2086_; lean_object* v_currNamespace_2087_; lean_object* v_openDecls_2088_; lean_object* v_initHeartbeats_2089_; lean_object* v_maxHeartbeats_2090_; lean_object* v_quotContext_2091_; lean_object* v_currMacroScope_2092_; uint8_t v_diag_2093_; lean_object* v_cancelTk_x3f_2094_; uint8_t v_suppressElabErrors_2095_; lean_object* v_inheritedTraceOptions_2096_; lean_object* v_ref_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_fileName_2081_ = lean_ctor_get(v___y_2078_, 0);
v_fileMap_2082_ = lean_ctor_get(v___y_2078_, 1);
v_options_2083_ = lean_ctor_get(v___y_2078_, 2);
v_currRecDepth_2084_ = lean_ctor_get(v___y_2078_, 3);
v_maxRecDepth_2085_ = lean_ctor_get(v___y_2078_, 4);
v_ref_2086_ = lean_ctor_get(v___y_2078_, 5);
v_currNamespace_2087_ = lean_ctor_get(v___y_2078_, 6);
v_openDecls_2088_ = lean_ctor_get(v___y_2078_, 7);
v_initHeartbeats_2089_ = lean_ctor_get(v___y_2078_, 8);
v_maxHeartbeats_2090_ = lean_ctor_get(v___y_2078_, 9);
v_quotContext_2091_ = lean_ctor_get(v___y_2078_, 10);
v_currMacroScope_2092_ = lean_ctor_get(v___y_2078_, 11);
v_diag_2093_ = lean_ctor_get_uint8(v___y_2078_, sizeof(void*)*14);
v_cancelTk_x3f_2094_ = lean_ctor_get(v___y_2078_, 12);
v_suppressElabErrors_2095_ = lean_ctor_get_uint8(v___y_2078_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2096_ = lean_ctor_get(v___y_2078_, 13);
v_ref_2097_ = l_Lean_replaceRef(v_ref_2072_, v_ref_2086_);
lean_inc_ref(v_inheritedTraceOptions_2096_);
lean_inc(v_cancelTk_x3f_2094_);
lean_inc(v_currMacroScope_2092_);
lean_inc(v_quotContext_2091_);
lean_inc(v_maxHeartbeats_2090_);
lean_inc(v_initHeartbeats_2089_);
lean_inc(v_openDecls_2088_);
lean_inc(v_currNamespace_2087_);
lean_inc(v_maxRecDepth_2085_);
lean_inc(v_currRecDepth_2084_);
lean_inc_ref(v_options_2083_);
lean_inc_ref(v_fileMap_2082_);
lean_inc_ref(v_fileName_2081_);
v___x_2098_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2098_, 0, v_fileName_2081_);
lean_ctor_set(v___x_2098_, 1, v_fileMap_2082_);
lean_ctor_set(v___x_2098_, 2, v_options_2083_);
lean_ctor_set(v___x_2098_, 3, v_currRecDepth_2084_);
lean_ctor_set(v___x_2098_, 4, v_maxRecDepth_2085_);
lean_ctor_set(v___x_2098_, 5, v_ref_2097_);
lean_ctor_set(v___x_2098_, 6, v_currNamespace_2087_);
lean_ctor_set(v___x_2098_, 7, v_openDecls_2088_);
lean_ctor_set(v___x_2098_, 8, v_initHeartbeats_2089_);
lean_ctor_set(v___x_2098_, 9, v_maxHeartbeats_2090_);
lean_ctor_set(v___x_2098_, 10, v_quotContext_2091_);
lean_ctor_set(v___x_2098_, 11, v_currMacroScope_2092_);
lean_ctor_set(v___x_2098_, 12, v_cancelTk_x3f_2094_);
lean_ctor_set(v___x_2098_, 13, v_inheritedTraceOptions_2096_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*14, v_diag_2093_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*14 + 1, v_suppressElabErrors_2095_);
v___x_2099_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___x_2098_, v___y_2079_);
lean_dec_ref_known(v___x_2098_, 14);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2100_, lean_object* v_msg_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2100_, v_msg_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v_ref_2100_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2110_, lean_object* v_options_2111_, lean_object* v_currNamespace_2112_, lean_object* v_openDecls_2113_, lean_object* v_n_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = l_Lean_ResolveName_resolveGlobalName(v_env_2110_, v_options_2111_, v_currNamespace_2112_, v_openDecls_2113_, v_n_2114_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2119_, lean_object* v_options_2120_, lean_object* v_currNamespace_2121_, lean_object* v_openDecls_2122_, lean_object* v_n_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2119_, v_options_2120_, v_currNamespace_2121_, v_openDecls_2122_, v_n_2123_, v___y_2124_, v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v_options_2120_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_2127_, lean_object* v___y_2128_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_a_2129_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_a_2129_);
lean_ctor_set(v___x_2130_, 1, v___y_2128_);
return v___x_2130_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_a_2131_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2131_);
lean_ctor_set(v___x_2132_, 1, v___y_2128_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2133_, v___y_2134_);
lean_dec_ref(v_x_2133_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2136_, lean_object* v_stx_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2136_, v_stx_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
if (lean_obj_tag(v_a_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2150_; 
v_a_2142_ = lean_ctor_get(v___x_2140_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v___x_2140_, 0);
lean_dec(v_unused_2151_);
v___x_2144_ = v___x_2140_;
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2140_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_box(0);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_a_2142_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
else
{
lean_object* v_val_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2180_; 
v_val_2152_ = lean_ctor_get(v_a_2141_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2154_ = v_a_2141_;
v_isShared_2155_ = v_isSharedCheck_2180_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_val_2152_);
lean_dec(v_a_2141_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2180_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_snd_2156_; 
v_snd_2156_ = lean_ctor_get(v_val_2152_, 1);
lean_inc(v_snd_2156_);
lean_dec(v_val_2152_);
if (lean_obj_tag(v_snd_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
lean_del_object(v___x_2154_);
v_a_2157_ = lean_ctor_get(v___x_2140_, 1);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2140_, 2);
v_a_2158_ = lean_ctor_get(v_snd_2156_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_snd_2156_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2160_ = v_snd_2156_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v_snd_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2163_, v_a_2157_);
lean_dec_ref(v___x_2163_);
return v___x_2164_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2179_; 
v_a_2167_ = lean_ctor_get(v___x_2140_, 1);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2140_, 2);
v_a_2168_ = lean_ctor_get(v_snd_2156_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_snd_2156_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2170_ = v_snd_2156_;
v_isShared_2171_ = v_isSharedCheck_2179_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v_snd_2156_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2179_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v_a_2168_);
v___x_2173_ = v___x_2154_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2175_ = v___x_2170_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2175_, v_a_2167_);
lean_dec_ref(v___x_2175_);
return v___x_2176_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2181_ = lean_ctor_get(v___x_2140_, 0);
v_a_2182_ = lean_ctor_get(v___x_2140_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2140_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_inc(v_a_2181_);
lean_dec(v___x_2140_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2181_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2190_, lean_object* v_stx_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2190_, v_stx_2191_, v___y_2192_, v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_currNamespace_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_currNamespace_2195_);
lean_ctor_set(v___x_2198_, 1, v___y_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_currNamespace_2199_, v___y_2200_, v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2202_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object* v_keys_2203_, lean_object* v_i_2204_, lean_object* v_k_2205_){
_start:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_array_get_size(v_keys_2203_);
v___x_2207_ = lean_nat_dec_lt(v_i_2204_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_dec(v_i_2204_);
return v___x_2207_;
}
else
{
lean_object* v_k_x27_2208_; uint8_t v___x_2209_; 
v_k_x27_2208_ = lean_array_fget_borrowed(v_keys_2203_, v_i_2204_);
v___x_2209_ = l_Lean_instBEqExtraModUse_beq(v_k_2205_, v_k_x27_2208_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_add(v_i_2204_, v___x_2210_);
lean_dec(v_i_2204_);
v_i_2204_ = v___x_2211_;
goto _start;
}
else
{
lean_dec(v_i_2204_);
return v___x_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object* v_keys_2213_, lean_object* v_i_2214_, lean_object* v_k_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2213_, v_i_2214_, v_k_2215_);
lean_dec_ref(v_k_2215_);
lean_dec_ref(v_keys_2213_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object* v_x_2218_, size_t v_x_2219_, lean_object* v_x_2220_){
_start:
{
if (lean_obj_tag(v_x_2218_) == 0)
{
lean_object* v_es_2221_; lean_object* v___x_2222_; size_t v___x_2223_; size_t v___x_2224_; lean_object* v_j_2225_; lean_object* v___x_2226_; 
v_es_2221_ = lean_ctor_get(v_x_2218_, 0);
v___x_2222_ = lean_box(2);
v___x_2223_ = ((size_t)31ULL);
v___x_2224_ = lean_usize_land(v_x_2219_, v___x_2223_);
v_j_2225_ = lean_usize_to_nat(v___x_2224_);
v___x_2226_ = lean_array_get_borrowed(v___x_2222_, v_es_2221_, v_j_2225_);
lean_dec(v_j_2225_);
switch(lean_obj_tag(v___x_2226_))
{
case 0:
{
lean_object* v_key_2227_; uint8_t v___x_2228_; 
v_key_2227_ = lean_ctor_get(v___x_2226_, 0);
v___x_2228_ = l_Lean_instBEqExtraModUse_beq(v_x_2220_, v_key_2227_);
return v___x_2228_;
}
case 1:
{
lean_object* v_node_2229_; size_t v___x_2230_; size_t v___x_2231_; 
v_node_2229_ = lean_ctor_get(v___x_2226_, 0);
v___x_2230_ = ((size_t)5ULL);
v___x_2231_ = lean_usize_shift_right(v_x_2219_, v___x_2230_);
v_x_2218_ = v_node_2229_;
v_x_2219_ = v___x_2231_;
goto _start;
}
default: 
{
uint8_t v___x_2233_; 
v___x_2233_ = 0;
return v___x_2233_;
}
}
}
else
{
lean_object* v_ks_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v_ks_2234_ = lean_ctor_get(v_x_2218_, 0);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_2234_, v___x_2235_, v_x_2220_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
size_t v_x_33792__boxed_2240_; uint8_t v_res_2241_; lean_object* v_r_2242_; 
v_x_33792__boxed_2240_ = lean_unbox_usize(v_x_2238_);
lean_dec(v_x_2238_);
v_res_2241_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2237_, v_x_33792__boxed_2240_, v_x_2239_);
lean_dec_ref(v_x_2239_);
lean_dec_ref(v_x_2237_);
v_r_2242_ = lean_box(v_res_2241_);
return v_r_2242_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object* v_x_2243_, lean_object* v_x_2244_){
_start:
{
uint64_t v___x_2245_; size_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2245_ = l_Lean_instHashableExtraModUse_hash(v_x_2244_);
v___x_2246_ = lean_uint64_to_usize(v___x_2245_);
v___x_2247_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2243_, v___x_2246_, v_x_2244_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object* v_x_2248_, lean_object* v_x_2249_){
_start:
{
uint8_t v_res_2250_; lean_object* v_r_2251_; 
v_res_2250_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2248_, v_x_2249_);
lean_dec_ref(v_x_2249_);
lean_dec_ref(v_x_2248_);
v_r_2251_ = lean_box(v_res_2250_);
return v_r_2251_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1));
v___x_2255_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0));
v___x_2256_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2255_, v___x_2254_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v_cls_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_cls_2268_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4));
v___x_2269_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2270_ = l_Lean_Name_append(v___x_2269_, v_cls_2268_);
return v___x_2270_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2281_, uint8_t v_isMeta_2282_, lean_object* v_hint_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v_env_2292_; uint8_t v_isExporting_2293_; lean_object* v___x_2294_; lean_object* v_env_2295_; lean_object* v___x_2296_; lean_object* v_entry_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2291_ = lean_st_ref_get(v___y_2289_);
v_env_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc_ref(v_env_2292_);
lean_dec(v___x_2291_);
v_isExporting_2293_ = lean_ctor_get_uint8(v_env_2292_, sizeof(void*)*8);
lean_dec_ref(v_env_2292_);
v___x_2294_ = lean_st_ref_get(v___y_2289_);
v_env_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc_ref(v_env_2295_);
lean_dec(v___x_2294_);
v___x_2296_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2);
lean_inc(v_mod_2281_);
v_entry_2297_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2297_, 0, v_mod_2281_);
lean_ctor_set_uint8(v_entry_2297_, sizeof(void*)*1, v_isExporting_2293_);
lean_ctor_set_uint8(v_entry_2297_, sizeof(void*)*1 + 1, v_isMeta_2282_);
v___x_2298_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2299_ = lean_box(1);
v___x_2300_ = lean_box(0);
v___x_2343_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2296_, v___x_2298_, v_env_2295_, v___x_2299_, v___x_2300_);
v___x_2344_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_2343_, v_entry_2297_);
lean_dec(v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v_options_2345_; uint8_t v_hasTrace_2346_; 
v_options_2345_ = lean_ctor_get(v___y_2288_, 2);
v_hasTrace_2346_ = lean_ctor_get_uint8(v_options_2345_, sizeof(void*)*1);
if (v_hasTrace_2346_ == 0)
{
lean_dec(v_hint_2283_);
lean_dec(v_mod_2281_);
v___y_2302_ = v___y_2287_;
v___y_2303_ = v___y_2289_;
goto v___jp_2301_;
}
else
{
lean_object* v_inheritedTraceOptions_2347_; lean_object* v_cls_2348_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_inheritedTraceOptions_2347_ = lean_ctor_get(v___y_2288_, 13);
v_cls_2348_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4));
v___x_2368_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
v___x_2369_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2347_, v_options_2345_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_dec(v_hint_2283_);
lean_dec(v_mod_2281_);
v___y_2302_ = v___y_2287_;
v___y_2303_ = v___y_2289_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2370_; lean_object* v___y_2372_; 
v___x_2370_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
if (v_isExporting_2293_ == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17));
v___y_2372_ = v___x_2379_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2380_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18));
v___y_2372_ = v___x_2380_;
goto v___jp_2371_;
}
v___jp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_inc_ref(v___y_2372_);
v___x_2373_ = l_Lean_stringToMessageData(v___y_2372_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2370_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
if (v_isMeta_2282_ == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2355_ = v___x_2376_;
v___y_2356_ = v___x_2377_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2378_; 
v___x_2378_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2355_ = v___x_2376_;
v___y_2356_ = v___x_2378_;
goto v___jp_2354_;
}
}
}
v___jp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2350_);
lean_ctor_set(v___x_2352_, 1, v___y_2351_);
v___x_2353_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2348_, v___x_2352_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_dec_ref_known(v___x_2353_, 1);
v___y_2302_ = v___y_2287_;
v___y_2303_ = v___y_2289_;
goto v___jp_2301_;
}
else
{
lean_dec_ref_known(v_entry_2297_, 1);
return v___x_2353_;
}
}
v___jp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
lean_inc_ref(v___y_2356_);
v___x_2357_ = l_Lean_stringToMessageData(v___y_2356_);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2355_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = l_Lean_MessageData_ofName(v_mod_2281_);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = l_Lean_Name_isAnonymous(v_hint_2283_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2365_ = l_Lean_MessageData_ofName(v_hint_2283_);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___y_2350_ = v___x_2362_;
v___y_2351_ = v___x_2366_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2367_; 
lean_dec(v_hint_2283_);
v___x_2367_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9);
v___y_2350_ = v___x_2362_;
v___y_2351_ = v___x_2367_;
goto v___jp_2349_;
}
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref_known(v_entry_2297_, 1);
lean_dec(v_hint_2283_);
lean_dec(v_mod_2281_);
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
v___jp_2301_:
{
lean_object* v___x_2304_; lean_object* v_toEnvExtension_2305_; lean_object* v_env_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_ngen_2308_; lean_object* v_auxDeclNGen_2309_; lean_object* v_traceState_2310_; lean_object* v_messages_2311_; lean_object* v_infoState_2312_; lean_object* v_snapshotTasks_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2341_; 
v___x_2304_ = lean_st_ref_take(v___y_2303_);
v_toEnvExtension_2305_ = lean_ctor_get(v___x_2298_, 0);
v_env_2306_ = lean_ctor_get(v___x_2304_, 0);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2304_, 1);
v_ngen_2308_ = lean_ctor_get(v___x_2304_, 2);
v_auxDeclNGen_2309_ = lean_ctor_get(v___x_2304_, 3);
v_traceState_2310_ = lean_ctor_get(v___x_2304_, 4);
v_messages_2311_ = lean_ctor_get(v___x_2304_, 6);
v_infoState_2312_ = lean_ctor_get(v___x_2304_, 7);
v_snapshotTasks_2313_ = lean_ctor_get(v___x_2304_, 8);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v___x_2304_, 5);
lean_dec(v_unused_2342_);
v___x_2315_ = v___x_2304_;
v_isShared_2316_ = v_isSharedCheck_2341_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snapshotTasks_2313_);
lean_inc(v_infoState_2312_);
lean_inc(v_messages_2311_);
lean_inc(v_traceState_2310_);
lean_inc(v_auxDeclNGen_2309_);
lean_inc(v_ngen_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2304_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2341_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_asyncMode_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v_asyncMode_2317_ = lean_ctor_get(v_toEnvExtension_2305_, 2);
v___x_2318_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2298_, v_env_2306_, v_entry_2297_, v_asyncMode_2317_, v___x_2300_);
v___x_2319_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 5, v___x_2319_);
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2321_ = v___x_2315_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_ngen_2308_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_auxDeclNGen_2309_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v_traceState_2310_);
lean_ctor_set(v_reuseFailAlloc_2340_, 5, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2340_, 6, v_messages_2311_);
lean_ctor_set(v_reuseFailAlloc_2340_, 7, v_infoState_2312_);
lean_ctor_set(v_reuseFailAlloc_2340_, 8, v_snapshotTasks_2313_);
v___x_2321_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_mctx_2324_; lean_object* v_zetaDeltaFVarIds_2325_; lean_object* v_postponed_2326_; lean_object* v_diag_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2338_; 
v___x_2322_ = lean_st_ref_put(v___y_2303_, v___x_2321_);
v___x_2323_ = lean_st_ref_take(v___y_2302_);
v_mctx_2324_ = lean_ctor_get(v___x_2323_, 0);
v_zetaDeltaFVarIds_2325_ = lean_ctor_get(v___x_2323_, 2);
v_postponed_2326_ = lean_ctor_get(v___x_2323_, 3);
v_diag_2327_ = lean_ctor_get(v___x_2323_, 4);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2323_, 1);
lean_dec(v_unused_2339_);
v___x_2329_ = v___x_2323_;
v_isShared_2330_ = v_isSharedCheck_2338_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_diag_2327_);
lean_inc(v_postponed_2326_);
lean_inc(v_zetaDeltaFVarIds_2325_);
lean_inc(v_mctx_2324_);
lean_dec(v___x_2323_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2338_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v___x_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_mctx_2324_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_zetaDeltaFVarIds_2325_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_postponed_2326_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_diag_2327_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_st_ref_put(v___y_2302_, v___x_2333_);
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2383_, lean_object* v_isMeta_2384_, lean_object* v_hint_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v_isMeta_boxed_2393_; lean_object* v_res_2394_; 
v_isMeta_boxed_2393_ = lean_unbox(v_isMeta_2384_);
v_res_2394_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2383_, v_isMeta_boxed_2393_, v_hint_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2395_, lean_object* v_declName_2396_, lean_object* v_as_2397_, size_t v_sz_2398_, size_t v_i_2399_, lean_object* v_b_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_usize_dec_lt(v_i_2399_, v_sz_2398_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec(v_declName_2396_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_b_2400_);
return v___x_2409_;
}
else
{
lean_object* v___x_2410_; lean_object* v_modules_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v_toImport_2415_; lean_object* v_module_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2410_ = l_Lean_Environment_header(v___x_2395_);
v_modules_2411_ = lean_ctor_get(v___x_2410_, 3);
lean_inc_ref(v_modules_2411_);
lean_dec_ref(v___x_2410_);
v___x_2412_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2413_ = lean_array_uget_borrowed(v_as_2397_, v_i_2399_);
v___x_2414_ = lean_array_get(v___x_2412_, v_modules_2411_, v_a_2413_);
lean_dec_ref(v_modules_2411_);
v_toImport_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_toImport_2415_);
lean_dec(v___x_2414_);
v_module_2416_ = lean_ctor_get(v_toImport_2415_, 0);
lean_inc(v_module_2416_);
lean_dec_ref(v_toImport_2415_);
v___x_2417_ = 0;
lean_inc(v_declName_2396_);
v___x_2418_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2416_, v___x_2417_, v_declName_2396_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; size_t v___x_2420_; size_t v___x_2421_; 
lean_dec_ref_known(v___x_2418_, 1);
v___x_2419_ = lean_box(0);
v___x_2420_ = ((size_t)1ULL);
v___x_2421_ = lean_usize_add(v_i_2399_, v___x_2420_);
v_i_2399_ = v___x_2421_;
v_b_2400_ = v___x_2419_;
goto _start;
}
else
{
lean_dec(v_declName_2396_);
return v___x_2418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2423_, lean_object* v_declName_2424_, lean_object* v_as_2425_, lean_object* v_sz_2426_, lean_object* v_i_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
size_t v_sz_boxed_2436_; size_t v_i_boxed_2437_; lean_object* v_res_2438_; 
v_sz_boxed_2436_ = lean_unbox_usize(v_sz_2426_);
lean_dec(v_sz_2426_);
v_i_boxed_2437_ = lean_unbox_usize(v_i_2427_);
lean_dec(v_i_2427_);
v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2423_, v_declName_2424_, v_as_2425_, v_sz_boxed_2436_, v_i_boxed_2437_, v_b_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_as_2425_);
lean_dec_ref(v___x_2423_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg(lean_object* v_m_2439_, lean_object* v_query_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_zero_2444_; uint8_t v_isZero_2445_; 
v_zero_2444_ = lean_unsigned_to_nat(0u);
v_isZero_2445_ = lean_nat_dec_eq(v_x_2442_, v_zero_2444_);
if (v_isZero_2445_ == 1)
{
lean_dec(v_x_2443_);
lean_dec(v_x_2442_);
if (lean_obj_tag(v_x_2441_) == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_box(2);
return v___x_2446_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_val_2447_ = lean_ctor_get(v_x_2441_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v_x_2441_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_val_2447_);
lean_dec(v_x_2441_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_val_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_keyArray_2455_; lean_object* v_valueArray_2456_; lean_object* v___x_2457_; uint8_t v_isSome_2458_; 
v_keyArray_2455_ = lean_ctor_get(v_m_2439_, 1);
v_valueArray_2456_ = lean_ctor_get(v_m_2439_, 2);
v___x_2457_ = lean_array_fget_borrowed(v_keyArray_2455_, v_x_2443_);
v_isSome_2458_ = lean_noption_is_some(v___x_2457_);
if (v_isSome_2458_ == 0)
{
lean_dec(v_x_2442_);
if (lean_obj_tag(v_x_2441_) == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_x_2443_);
return v___x_2459_;
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_x_2443_);
v_val_2460_ = lean_ctor_get(v_x_2441_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v_x_2441_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_val_2460_);
lean_dec(v_x_2441_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_val_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_one_2468_; lean_object* v_n_2469_; lean_object* v___y_2471_; 
v_one_2468_ = lean_unsigned_to_nat(1u);
v_n_2469_ = lean_nat_sub(v_x_2442_, v_one_2468_);
lean_dec(v_x_2442_);
if (v_isSome_2458_ == 0)
{
goto v___jp_2477_;
}
else
{
lean_object* v___x_2479_; uint8_t v_isSome_2480_; 
v___x_2479_ = lean_array_fget_borrowed(v_valueArray_2456_, v_x_2443_);
v_isSome_2480_ = lean_noption_is_some(v___x_2479_);
if (v_isSome_2480_ == 0)
{
goto v___jp_2477_;
}
else
{
lean_object* v_val_2481_; uint8_t v___x_2482_; 
lean_inc(v___x_2457_);
v_val_2481_ = lean_noption_get(v___x_2457_);
v___x_2482_ = lean_name_eq(v_val_2481_, v_query_2440_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
lean_dec(v_val_2481_);
v___x_2483_ = lean_array_get_size(v_keyArray_2455_);
v___x_2484_ = lean_nat_add(v_x_2443_, v_one_2468_);
lean_dec(v_x_2443_);
v___x_2485_ = lean_nat_dec_lt(v___x_2484_, v___x_2483_);
if (v___x_2485_ == 0)
{
lean_dec(v___x_2484_);
v_x_2442_ = v_n_2469_;
v_x_2443_ = v_zero_2444_;
goto _start;
}
else
{
v_x_2442_ = v_n_2469_;
v_x_2443_ = v___x_2484_;
goto _start;
}
}
else
{
lean_object* v_val_2488_; lean_object* v___x_2489_; 
lean_dec(v_n_2469_);
lean_dec(v_x_2441_);
lean_inc(v___x_2479_);
v_val_2488_ = lean_noption_get(v___x_2479_);
v___x_2489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2489_, 0, v_x_2443_);
lean_ctor_set(v___x_2489_, 1, v_val_2481_);
lean_ctor_set(v___x_2489_, 2, v_val_2488_);
return v___x_2489_;
}
}
}
v___jp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2472_ = lean_array_get_size(v_keyArray_2455_);
v___x_2473_ = lean_nat_add(v_x_2443_, v_one_2468_);
lean_dec(v_x_2443_);
v___x_2474_ = lean_nat_dec_lt(v___x_2473_, v___x_2472_);
if (v___x_2474_ == 0)
{
lean_dec(v___x_2473_);
v_x_2441_ = v___y_2471_;
v_x_2442_ = v_n_2469_;
v_x_2443_ = v_zero_2444_;
goto _start;
}
else
{
v_x_2441_ = v___y_2471_;
v_x_2442_ = v_n_2469_;
v_x_2443_ = v___x_2473_;
goto _start;
}
}
v___jp_2477_:
{
if (lean_obj_tag(v_x_2441_) == 0)
{
lean_object* v___x_2478_; 
lean_inc(v_x_2443_);
v___x_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_x_2443_);
v___y_2471_ = v___x_2478_;
goto v___jp_2470_;
}
else
{
v___y_2471_ = v_x_2441_;
goto v___jp_2470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg___boxed(lean_object* v_m_2490_, lean_object* v_query_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg(v_m_2490_, v_query_2491_, v_x_2492_, v_x_2493_, v_x_2494_);
lean_dec(v_query_2491_);
lean_dec_ref(v_m_2490_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg(lean_object* v_m_2496_, lean_object* v_query_2497_){
_start:
{
lean_object* v_keyArray_2498_; lean_object* v___x_2499_; uint64_t v___y_2501_; 
v_keyArray_2498_ = lean_ctor_get(v_m_2496_, 1);
v___x_2499_ = lean_array_get_size(v_keyArray_2498_);
if (lean_obj_tag(v_query_2497_) == 0)
{
uint64_t v___x_2516_; 
v___x_2516_ = 1723ULL;
v___y_2501_ = v___x_2516_;
goto v___jp_2500_;
}
else
{
uint64_t v_hash_2517_; 
v_hash_2517_ = lean_ctor_get_uint64(v_query_2497_, sizeof(void*)*2);
v___y_2501_ = v_hash_2517_;
goto v___jp_2500_;
}
v___jp_2500_:
{
uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v_fold_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; uint64_t v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; size_t v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2502_ = 32ULL;
v___x_2503_ = lean_uint64_shift_right(v___y_2501_, v___x_2502_);
v_fold_2504_ = lean_uint64_xor(v___y_2501_, v___x_2503_);
v___x_2505_ = 16ULL;
v___x_2506_ = lean_uint64_shift_right(v_fold_2504_, v___x_2505_);
v___x_2507_ = lean_uint64_xor(v_fold_2504_, v___x_2506_);
v___x_2508_ = lean_uint64_to_usize(v___x_2507_);
v___x_2509_ = lean_usize_of_nat(v___x_2499_);
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_sub(v___x_2509_, v___x_2510_);
v___x_2512_ = lean_usize_land(v___x_2508_, v___x_2511_);
v___x_2513_ = lean_usize_to_nat(v___x_2512_);
v___x_2514_ = lean_box(0);
v___x_2515_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg(v_m_2496_, v_query_2497_, v___x_2514_, v___x_2499_, v___x_2513_);
return v___x_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg___boxed(lean_object* v_m_2518_, lean_object* v_query_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg(v_m_2518_, v_query_2519_);
lean_dec(v_query_2519_);
lean_dec_ref(v_m_2518_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object* v_m_2521_, lean_object* v_query_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg(v_m_2521_, v_query_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_index_2524_; lean_object* v_key_2525_; lean_object* v_value_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_index_2524_ = lean_ctor_get(v___x_2523_, 0);
v_key_2525_ = lean_ctor_get(v___x_2523_, 1);
v_value_2526_ = lean_ctor_get(v___x_2523_, 2);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2523_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_value_2526_);
lean_inc(v_key_2525_);
lean_inc(v_index_2524_);
lean_dec(v___x_2523_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_index_2524_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_key_2525_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_value_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v___x_2523_);
v___x_2534_ = lean_box(1);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object* v_m_2535_, lean_object* v_query_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_m_2535_, v_query_2536_);
lean_dec(v_query_2536_);
lean_dec_ref(v_m_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_m_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_value_2541_; lean_object* v___x_2542_; 
v_value_2541_ = lean_ctor_get(v___x_2540_, 2);
lean_inc(v_value_2541_);
lean_dec_ref_known(v___x_2540_, 3);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_value_2541_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_box(0);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_m_2544_);
return v_res_2546_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___x_2550_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0));
v___x_2551_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2550_, v___x_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2554_, uint8_t v_isMeta_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v_env_2567_; lean_object* v___y_2569_; lean_object* v___x_2582_; 
v___x_2563_ = lean_st_ref_get(v___y_2561_);
v_env_2567_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_ref(v_env_2567_);
lean_dec(v___x_2563_);
v___x_2582_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2567_, v_declName_2554_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_dec_ref(v_env_2567_);
lean_dec(v_declName_2554_);
goto v___jp_2564_;
}
else
{
lean_object* v_val_2583_; lean_object* v___x_2584_; lean_object* v_modules_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_val_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_val_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = l_Lean_Environment_header(v_env_2567_);
v_modules_2585_ = lean_ctor_get(v___x_2584_, 3);
lean_inc_ref(v_modules_2585_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = lean_array_get_size(v_modules_2585_);
v___x_2587_ = lean_nat_dec_lt(v_val_2583_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_dec_ref(v_modules_2585_);
lean_dec(v_val_2583_);
lean_dec_ref(v_env_2567_);
lean_dec(v_declName_2554_);
goto v___jp_2564_;
}
else
{
lean_object* v___x_2588_; lean_object* v_env_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___y_2593_; 
v___x_2588_ = lean_st_ref_get(v___y_2561_);
v_env_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc_ref(v_env_2589_);
lean_dec(v___x_2588_);
v___x_2590_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2);
v___x_2591_ = lean_array_fget(v_modules_2585_, v_val_2583_);
lean_dec(v_val_2583_);
lean_dec_ref(v_modules_2585_);
if (v_isMeta_2555_ == 0)
{
lean_dec_ref(v_env_2589_);
v___y_2593_ = v_isMeta_2555_;
goto v___jp_2592_;
}
else
{
uint8_t v___x_2604_; 
lean_inc(v_declName_2554_);
v___x_2604_ = l_Lean_isMarkedMeta(v_env_2589_, v_declName_2554_);
if (v___x_2604_ == 0)
{
v___y_2593_ = v_isMeta_2555_;
goto v___jp_2592_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = 0;
v___y_2593_ = v___x_2605_;
goto v___jp_2592_;
}
}
v___jp_2592_:
{
lean_object* v_toImport_2594_; lean_object* v_module_2595_; lean_object* v___x_2596_; 
v_toImport_2594_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_ref(v_toImport_2594_);
lean_dec(v___x_2591_);
v_module_2595_ = lean_ctor_get(v_toImport_2594_, 0);
lean_inc(v_module_2595_);
lean_dec_ref(v_toImport_2594_);
lean_inc(v_declName_2554_);
v___x_2596_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2595_, v___y_2593_, v_declName_2554_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref_known(v___x_2596_, 1);
v___x_2597_ = l_Lean_indirectModUseExt;
v___x_2598_ = lean_box(1);
v___x_2599_ = lean_box(0);
lean_inc_ref(v_env_2567_);
v___x_2600_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2590_, v___x_2597_, v_env_2567_, v___x_2598_, v___x_2599_);
v___x_2601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2600_, v_declName_2554_);
lean_dec(v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3));
v___y_2569_ = v___x_2602_;
goto v___jp_2568_;
}
else
{
lean_object* v_val_2603_; 
v_val_2603_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2601_, 1);
v___y_2569_ = v_val_2603_;
goto v___jp_2568_;
}
}
else
{
lean_dec_ref(v_env_2567_);
lean_dec(v_declName_2554_);
return v___x_2596_;
}
}
}
}
v___jp_2564_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
v___jp_2568_:
{
lean_object* v___x_2570_; size_t v_sz_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2570_ = lean_box(0);
v_sz_2571_ = lean_array_size(v___y_2569_);
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2567_, v_declName_2554_, v___y_2569_, v_sz_2571_, v___x_2572_, v___x_2570_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_env_2567_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v___x_2573_, 0);
lean_dec(v_unused_2581_);
v___x_2575_ = v___x_2573_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_dec(v___x_2573_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2570_);
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2570_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
return v___x_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2606_, lean_object* v_isMeta_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
uint8_t v_isMeta_boxed_2615_; lean_object* v_res_2616_; 
v_isMeta_boxed_2615_ = lean_unbox(v_isMeta_2607_);
v_res_2616_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2606_, v_isMeta_boxed_2615_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
if (lean_obj_tag(v_as_x27_2617_) == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_b_2618_);
return v___x_2626_;
}
else
{
lean_object* v_head_2627_; lean_object* v_tail_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; 
v_head_2627_ = lean_ctor_get(v_as_x27_2617_, 0);
v_tail_2628_ = lean_ctor_get(v_as_x27_2617_, 1);
v___x_2629_ = 1;
lean_inc(v_head_2627_);
v___x_2630_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2627_, v___x_2629_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref_known(v___x_2630_, 1);
v___x_2631_ = lean_box(0);
v_as_x27_2617_ = v_tail_2628_;
v_b_2618_ = v___x_2631_;
goto _start;
}
else
{
return v___x_2630_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2633_, v_b_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v_as_x27_2633_);
return v_res_2642_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = l_Lean_maxRecDepthErrorMessage;
v___x_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2651_ = l_Lean_MessageData_ofFormat(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2653_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2654_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___x_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_ref_2655_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v_env_2673_; lean_object* v_options_2674_; lean_object* v_currRecDepth_2675_; lean_object* v_maxRecDepth_2676_; lean_object* v_ref_2677_; lean_object* v_currNamespace_2678_; lean_object* v_openDecls_2679_; lean_object* v_quotContext_2680_; lean_object* v_currMacroScope_2681_; lean_object* v___x_2682_; lean_object* v_nextMacroScope_2683_; lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___f_2686_; lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v_methods_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2672_ = lean_st_ref_get(v___y_2670_);
v_env_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_ref_n(v_env_2673_, 4);
lean_dec(v___x_2672_);
v_options_2674_ = lean_ctor_get(v___y_2669_, 2);
v_currRecDepth_2675_ = lean_ctor_get(v___y_2669_, 3);
v_maxRecDepth_2676_ = lean_ctor_get(v___y_2669_, 4);
v_ref_2677_ = lean_ctor_get(v___y_2669_, 5);
v_currNamespace_2678_ = lean_ctor_get(v___y_2669_, 6);
v_openDecls_2679_ = lean_ctor_get(v___y_2669_, 7);
v_quotContext_2680_ = lean_ctor_get(v___y_2669_, 10);
v_currMacroScope_2681_ = lean_ctor_get(v___y_2669_, 11);
v___x_2682_ = lean_st_ref_get(v___y_2670_);
v_nextMacroScope_2683_ = lean_ctor_get(v___x_2682_, 1);
lean_inc(v_nextMacroScope_2683_);
lean_dec(v___x_2682_);
v___f_2684_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2684_, 0, v_env_2673_);
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2685_, 0, v_env_2673_);
lean_inc_n(v_openDecls_2679_, 2);
lean_inc_n(v_currNamespace_2678_, 3);
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2686_, 0, v_env_2673_);
lean_closure_set(v___f_2686_, 1, v_currNamespace_2678_);
lean_closure_set(v___f_2686_, 2, v_openDecls_2679_);
v___f_2687_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2687_, 0, v_currNamespace_2678_);
lean_inc_ref(v_options_2674_);
v___f_2688_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2688_, 0, v_env_2673_);
lean_closure_set(v___f_2688_, 1, v_options_2674_);
lean_closure_set(v___f_2688_, 2, v_currNamespace_2678_);
lean_closure_set(v___f_2688_, 3, v_openDecls_2679_);
v_methods_2689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2689_, 0, v___f_2684_);
lean_ctor_set(v_methods_2689_, 1, v___f_2687_);
lean_ctor_set(v_methods_2689_, 2, v___f_2685_);
lean_ctor_set(v_methods_2689_, 3, v___f_2686_);
lean_ctor_set(v_methods_2689_, 4, v___f_2688_);
lean_inc(v_ref_2677_);
lean_inc(v_maxRecDepth_2676_);
lean_inc(v_currRecDepth_2675_);
lean_inc(v_currMacroScope_2681_);
lean_inc(v_quotContext_2680_);
v___x_2690_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2690_, 0, v_methods_2689_);
lean_ctor_set(v___x_2690_, 1, v_quotContext_2680_);
lean_ctor_set(v___x_2690_, 2, v_currMacroScope_2681_);
lean_ctor_set(v___x_2690_, 3, v_currRecDepth_2675_);
lean_ctor_set(v___x_2690_, 4, v_maxRecDepth_2676_);
lean_ctor_set(v___x_2690_, 5, v_ref_2677_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2692_, 0, v_nextMacroScope_2683_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_ctor_set(v___x_2692_, 2, v___x_2691_);
v___x_2693_ = lean_apply_2(v_x_2664_, v___x_2690_, v___x_2692_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_a_2695_; lean_object* v_macroScope_2696_; lean_object* v_traceMsgs_2697_; lean_object* v_expandedMacroDecls_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 1);
lean_inc(v_a_2694_);
v_a_2695_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2693_, 2);
v_macroScope_2696_ = lean_ctor_get(v_a_2694_, 0);
lean_inc(v_macroScope_2696_);
v_traceMsgs_2697_ = lean_ctor_get(v_a_2694_, 1);
lean_inc(v_traceMsgs_2697_);
v_expandedMacroDecls_2698_ = lean_ctor_get(v_a_2694_, 2);
lean_inc(v_expandedMacroDecls_2698_);
lean_dec(v_a_2694_);
v___x_2699_ = lean_box(0);
v___x_2700_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2698_, v___x_2699_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v_expandedMacroDecls_2698_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v___x_2701_; lean_object* v_env_2702_; lean_object* v_ngen_2703_; lean_object* v_auxDeclNGen_2704_; lean_object* v_traceState_2705_; lean_object* v_cache_2706_; lean_object* v_messages_2707_; lean_object* v_infoState_2708_; lean_object* v_snapshotTasks_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref_known(v___x_2700_, 1);
v___x_2701_ = lean_st_ref_take(v___y_2670_);
v_env_2702_ = lean_ctor_get(v___x_2701_, 0);
v_ngen_2703_ = lean_ctor_get(v___x_2701_, 2);
v_auxDeclNGen_2704_ = lean_ctor_get(v___x_2701_, 3);
v_traceState_2705_ = lean_ctor_get(v___x_2701_, 4);
v_cache_2706_ = lean_ctor_get(v___x_2701_, 5);
v_messages_2707_ = lean_ctor_get(v___x_2701_, 6);
v_infoState_2708_ = lean_ctor_get(v___x_2701_, 7);
v_snapshotTasks_2709_ = lean_ctor_get(v___x_2701_, 8);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2701_, 1);
lean_dec(v_unused_2736_);
v___x_2711_ = v___x_2701_;
v_isShared_2712_ = v_isSharedCheck_2735_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snapshotTasks_2709_);
lean_inc(v_infoState_2708_);
lean_inc(v_messages_2707_);
lean_inc(v_cache_2706_);
lean_inc(v_traceState_2705_);
lean_inc(v_auxDeclNGen_2704_);
lean_inc(v_ngen_2703_);
lean_inc(v_env_2702_);
lean_dec(v___x_2701_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2735_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_macroScope_2696_);
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_env_2702_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_macroScope_2696_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_ngen_2703_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v_auxDeclNGen_2704_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_traceState_2705_);
lean_ctor_set(v_reuseFailAlloc_2734_, 5, v_cache_2706_);
lean_ctor_set(v_reuseFailAlloc_2734_, 6, v_messages_2707_);
lean_ctor_set(v_reuseFailAlloc_2734_, 7, v_infoState_2708_);
lean_ctor_set(v_reuseFailAlloc_2734_, 8, v_snapshotTasks_2709_);
v___x_2714_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_st_ref_put(v___y_2670_, v___x_2714_);
v___x_2716_ = l_List_reverse___redArg(v_traceMsgs_2697_);
v___x_2717_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2716_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
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
lean_ctor_set(v___x_2719_, 0, v_a_2695_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2695_);
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
lean_dec(v_a_2695_);
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
lean_dec(v_traceMsgs_2697_);
lean_dec(v_macroScope_2696_);
lean_dec(v_a_2695_);
v_a_2737_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2700_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2700_);
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
v_a_2745_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2693_, 2);
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
v___x_2752_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2746_, v___x_2751_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
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
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_2764_, lean_object* v_n_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2773_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2774_ = lean_box_uint64(v_h_2764_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_n_2765_);
v___x_2776_ = 2;
v___x_2777_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_2773_, v___x_2775_, v___x_2776_, v___y_2769_, v___y_2770_, v___y_2771_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_2778_, lean_object* v_n_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
uint64_t v_h_boxed_2787_; lean_object* v_res_2788_; 
v_h_boxed_2787_ = lean_unbox_uint64(v_h_2778_);
lean_dec_ref(v_h_2778_);
v_res_2788_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_2787_, v_n_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2788_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_box(0);
v___x_2793_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2794_ = l_Lean_mkConst(v___x_2793_, v___x_2792_);
return v___x_2794_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2805_ = l_Lean_mkConst(v___x_2804_, v___x_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2808_, lean_object* v_as_2809_, size_t v_sz_2810_, size_t v_i_2811_, lean_object* v_b_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_a_2821_; uint8_t v___x_2825_; 
v___x_2825_ = lean_usize_dec_lt(v_i_2811_, v_sz_2810_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_b_2812_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_a_2829_; uint8_t v___x_2830_; 
v___x_2827_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2828_ = lean_box(0);
v_a_2829_ = lean_array_uget_borrowed(v_as_2809_, v_i_2811_);
lean_inc(v_a_2829_);
v___x_2830_ = l_Lean_Syntax_isOfKind(v_a_2829_, v___x_2827_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2831_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = l_Lean_Syntax_getArg(v_a_2829_, v___x_2832_);
v___x_2835_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2834_);
v___x_2836_ = l_Lean_Syntax_isOfKind(v___x_2834_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2834_);
v___x_2838_ = l_Lean_Syntax_isOfKind(v___x_2834_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
lean_dec(v___x_2834_);
v___x_2839_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_dec_ref_known(v___x_2839_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2839_;
}
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = l_Lean_Syntax_getArg(v___x_2834_, v___x_2832_);
v___x_2841_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2840_);
v___x_2842_ = l_Lean_Syntax_isOfKind(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec(v___x_2840_);
lean_dec(v___x_2834_);
v___x_2843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_dec_ref_known(v___x_2843_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2843_;
}
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2844_ = l_Lean_Syntax_getArg(v___x_2834_, v___x_2833_);
lean_dec(v___x_2834_);
v___x_2845_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2844_);
v___x_2846_ = l_Lean_Syntax_isOfKind(v___x_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; 
lean_dec(v___x_2844_);
lean_dec(v___x_2840_);
v___x_2847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_dec_ref_known(v___x_2847_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2847_;
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2848_, 0, v___x_2840_);
v___x_2849_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2848_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l_Lean_Widget_elabWidgetInstanceSpec(v___x_2844_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2853_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc_n(v_a_2852_, 2);
lean_dec_ref_known(v___x_2851_, 1);
v___x_2853_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2852_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2853_) == 0)
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_unbox(v_a_2850_);
if (v___x_2854_ == 1)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
lean_dec(v_a_2852_);
lean_dec(v_a_2850_);
v_a_2855_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2856_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2855_, v___y_2816_, v___y_2818_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_dec_ref_known(v___x_2856_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2856_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v_id_2858_; uint64_t v_javascriptHash_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_a_2857_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2853_, 1);
v_id_2858_ = lean_ctor_get(v_a_2857_, 0);
lean_inc(v_id_2858_);
v_javascriptHash_2859_ = lean_ctor_get_uint64(v_a_2857_, sizeof(void*)*2);
lean_dec(v_a_2857_);
v___x_2860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1));
v___x_2861_ = l_Lean_Name_append(v_id_2858_, v___x_2860_);
v___x_2862_ = l_Lean_Core_mkFreshUserName(v___x_2861_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2864_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2852_, v___y_2816_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___x_2885_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = lean_box(0);
v___x_2885_ = l_Lean_Expr_hasMVar(v_a_2865_);
if (v___x_2885_ == 0)
{
v___y_2868_ = v___y_2813_;
v___y_2869_ = v___y_2814_;
v___y_2870_ = v___y_2815_;
v___y_2871_ = v___y_2816_;
v___y_2872_ = v___y_2817_;
v___y_2873_ = v___y_2818_;
goto v___jp_2867_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2865_);
v___x_2887_ = l_Lean_indentExpr(v_a_2865_);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2888_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_dec_ref_known(v___x_2889_, 1);
v___y_2868_ = v___y_2813_;
v___y_2869_ = v___y_2814_;
v___y_2870_ = v___y_2815_;
v___y_2871_ = v___y_2816_;
v___y_2872_ = v___y_2817_;
v___y_2873_ = v___y_2818_;
goto v___jp_2867_;
}
else
{
lean_dec(v_a_2865_);
lean_dec(v_a_2863_);
lean_dec(v_a_2850_);
return v___x_2889_;
}
}
v___jp_2867_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
lean_inc_n(v_a_2863_, 2);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v_a_2863_);
lean_ctor_set(v___x_2875_, 1, v___x_2866_);
lean_ctor_set(v___x_2875_, 2, v___x_2874_);
v___x_2876_ = lean_box(0);
v___x_2877_ = 1;
v___x_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2878_, 0, v_a_2863_);
lean_ctor_set(v___x_2878_, 1, v___x_2866_);
v___x_2879_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2875_);
lean_ctor_set(v___x_2879_, 1, v_a_2865_);
lean_ctor_set(v___x_2879_, 2, v___x_2876_);
lean_ctor_set(v___x_2879_, 3, v___x_2878_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*4, v___x_2877_);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = l_Lean_addAndCompile(v___x_2880_, v___x_2808_, v___x_2836_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2881_) == 0)
{
uint8_t v___x_2882_; 
lean_dec_ref_known(v___x_2881_, 1);
v___x_2882_ = lean_unbox(v_a_2850_);
lean_dec(v_a_2850_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_2859_, v_a_2863_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_dec_ref_known(v___x_2883_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2883_;
}
}
else
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_2859_, v_a_2863_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_dec_ref_known(v___x_2884_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2884_;
}
}
}
else
{
lean_dec(v_a_2863_);
lean_dec(v_a_2850_);
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2863_);
lean_dec(v_a_2850_);
v_a_2890_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2864_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2864_);
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
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_a_2852_);
lean_dec(v_a_2850_);
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
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2852_);
lean_dec(v_a_2850_);
v_a_2906_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2853_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2853_);
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
lean_dec(v_a_2850_);
v_a_2914_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2851_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2851_);
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
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v___x_2844_);
v_a_2922_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2849_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2849_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2930_ = l_Lean_Syntax_getArg(v___x_2834_, v___x_2833_);
lean_dec(v___x_2834_);
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
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2933_;
}
}
else
{
lean_object* v_ref_2934_; lean_object* v_quotContext_2935_; lean_object* v_currMacroScope_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_ref_2934_ = lean_ctor_get(v___y_2817_, 5);
v_quotContext_2935_ = lean_ctor_get(v___y_2817_, 10);
v_currMacroScope_2936_ = lean_ctor_get(v___y_2817_, 11);
v___x_2937_ = 0;
v___x_2938_ = l_Lean_SourceInfo_fromRef(v_ref_2934_, v___x_2937_);
v___x_2939_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2940_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2941_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2936_);
lean_inc(v_quotContext_2935_);
v___x_2942_ = l_Lean_addMacroScope(v_quotContext_2935_, v___x_2941_, v_currMacroScope_2936_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2938_, 2);
v___x_2944_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2938_);
lean_ctor_set(v___x_2944_, 1, v___x_2940_);
lean_ctor_set(v___x_2944_, 2, v___x_2942_);
lean_ctor_set(v___x_2944_, 3, v___x_2943_);
v___x_2945_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2946_ = l_Lean_Syntax_node1(v___x_2938_, v___x_2945_, v___x_2930_);
v___x_2947_ = l_Lean_Syntax_node2(v___x_2938_, v___x_2939_, v___x_2944_, v___x_2946_);
v___x_2948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2949_ = l_Lean_Elab_Term_elabTerm(v___x_2947_, v___x_2948_, v___x_2808_, v___x_2808_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2950_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; uint64_t v_javascriptHash_2953_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v_javascriptHash_2953_ = lean_ctor_get_uint64(v_a_2952_, sizeof(void*)*1);
lean_dec(v_a_2952_);
v___x_2954_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2953_, v___y_2816_, v___y_2818_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_dec_ref_known(v___x_2954_, 1);
v_a_2821_ = v___x_2828_;
goto v___jp_2820_;
}
else
{
return v___x_2954_;
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
v_a_2955_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2951_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2951_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
v_a_2963_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2949_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2949_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
}
}
v___jp_2820_:
{
size_t v___x_2822_; size_t v___x_2823_; 
v___x_2822_ = ((size_t)1ULL);
v___x_2823_ = lean_usize_add(v_i_2811_, v___x_2822_);
v_i_2811_ = v___x_2823_;
v_b_2812_ = v_a_2821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2971_, lean_object* v_as_2972_, lean_object* v_sz_2973_, lean_object* v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
uint8_t v___x_34804__boxed_2983_; size_t v_sz_boxed_2984_; size_t v_i_boxed_2985_; lean_object* v_res_2986_; 
v___x_34804__boxed_2983_ = lean_unbox(v___x_2971_);
v_sz_boxed_2984_ = lean_unbox_usize(v_sz_2973_);
lean_dec(v_sz_2973_);
v_i_boxed_2985_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_res_2986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_34804__boxed_2983_, v_as_2972_, v_sz_boxed_2984_, v_i_boxed_2985_, v_b_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_as_2972_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2987_, lean_object* v___x_2988_, size_t v_sz_2989_, size_t v___x_2990_, lean_object* v___x_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2987_, v___x_2988_, v_sz_2989_, v___x_2990_, v___x_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3007_);
v___x_3001_ = v___x_2999_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v___x_2999_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_2991_);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2991_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_3008_, lean_object* v___x_3009_, lean_object* v_sz_3010_, lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
uint8_t v___x_35156__boxed_3020_; size_t v_sz_boxed_3021_; size_t v___x_35158__boxed_3022_; lean_object* v_res_3023_; 
v___x_35156__boxed_3020_ = lean_unbox(v___x_3008_);
v_sz_boxed_3021_ = lean_unbox_usize(v_sz_3010_);
lean_dec(v_sz_3010_);
v___x_35158__boxed_3022_ = lean_unbox_usize(v___x_3011_);
lean_dec(v___x_3011_);
v_res_3023_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_35156__boxed_3020_, v___x_3009_, v_sz_boxed_3021_, v___x_35158__boxed_3022_, v___x_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v___x_3009_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_3026_);
v___x_3031_ = l_Lean_Syntax_isOfKind(v_x_3026_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec(v_x_3026_);
v___x_3032_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3032_;
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v_ws_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; size_t v_sz_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___f_3042_; lean_object* v___x_3043_; 
v___x_3033_ = lean_unsigned_to_nat(2u);
v___x_3034_ = l_Lean_Syntax_getArg(v_x_3026_, v___x_3033_);
lean_dec(v_x_3026_);
v_ws_3035_ = l_Lean_Syntax_getArgs(v___x_3034_);
lean_dec(v___x_3034_);
v___x_3036_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_3035_);
lean_dec_ref(v_ws_3035_);
v___x_3037_ = lean_box(0);
v_sz_3038_ = lean_array_size(v___x_3036_);
v___x_3039_ = lean_box(v___x_3031_);
v___x_3040_ = lean_box_usize(v_sz_3038_);
v___x_3041_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_3042_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3042_, 0, v___x_3039_);
lean_closure_set(v___f_3042_, 1, v___x_3036_);
lean_closure_set(v___f_3042_, 2, v___x_3040_);
lean_closure_set(v___f_3042_, 3, v___x_3041_);
lean_closure_set(v___f_3042_, 4, v___x_3037_);
v___x_3043_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3042_, v_a_3027_, v_a_3028_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_3044_, v_a_3045_, v_a_3046_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_3049_, lean_object* v_x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_3050_, v___y_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_3054_, v_x_3055_, v___y_3056_, v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v_x_3055_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_3059_, lean_object* v_ref_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_3060_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3069_, lean_object* v_ref_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3069_, v_ref_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3079_, lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3089_, v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3099_, v___y_3103_, v___y_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object* v_00_u03b1_3117_, lean_object* v_00_u03b2_3118_, lean_object* v_00_u03c3_3119_, lean_object* v_ext_3120_, lean_object* v_b_3121_, uint8_t v_kind_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_3120_, v_b_3121_, v_kind_3122_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object* v_00_u03b1_3131_, lean_object* v_00_u03b2_3132_, lean_object* v_00_u03c3_3133_, lean_object* v_ext_3134_, lean_object* v_b_3135_, lean_object* v_kind_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
uint8_t v_kind_boxed_3144_; lean_object* v_res_3145_; 
v_kind_boxed_3144_ = lean_unbox(v_kind_3136_);
v_res_3145_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_3131_, v_00_u03b2_3132_, v_00_u03c3_3133_, v_ext_3134_, v_b_3135_, v_kind_boxed_3144_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3146_, lean_object* v_msg_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3156_, lean_object* v_msg_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3156_, v_msg_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3166_, v___y_3170_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
uint64_t v_h_boxed_3183_; lean_object* v_res_3184_; 
v_h_boxed_3183_ = lean_unbox_uint64(v_h_3175_);
lean_dec_ref(v_h_3175_);
v_res_3184_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3183_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3185_, lean_object* v_msg_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3185_, v_msg_3186_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3195_, lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3195_, v_msg_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3205_, lean_object* v_as_x27_3206_, lean_object* v_b_3207_, lean_object* v_a_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3206_, v_b_3207_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3217_, lean_object* v_as_x27_3218_, lean_object* v_b_3219_, lean_object* v_a_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3217_, v_as_x27_3218_, v_b_3219_, v_a_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v_as_x27_3218_);
lean_dec(v_as_3217_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3229_, lean_object* v_ref_3230_, lean_object* v_msg_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3230_, v_msg_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3240_, lean_object* v_ref_3241_, lean_object* v_msg_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3240_, v_ref_3241_, v_msg_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v_ref_3241_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3251_, lean_object* v_t_3252_, uint64_t v_k_3253_, lean_object* v_fallback_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3252_, v_k_3253_, v_fallback_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3256_, lean_object* v_t_3257_, lean_object* v_k_3258_, lean_object* v_fallback_3259_){
_start:
{
uint64_t v_k_boxed_3260_; lean_object* v_res_3261_; 
v_k_boxed_3260_ = lean_unbox_uint64(v_k_3258_);
lean_dec_ref(v_k_3258_);
v_res_3261_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3256_, v_t_3257_, v_k_boxed_3260_, v_fallback_3259_);
lean_dec(v_fallback_3259_);
lean_dec(v_t_3257_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3262_, uint64_t v_k_3263_, lean_object* v_v_3264_, lean_object* v_t_3265_, lean_object* v_hl_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3263_, v_v_3264_, v_t_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3268_, lean_object* v_k_3269_, lean_object* v_v_3270_, lean_object* v_t_3271_, lean_object* v_hl_3272_){
_start:
{
uint64_t v_k_boxed_3273_; lean_object* v_res_3274_; 
v_k_boxed_3273_ = lean_unbox_uint64(v_k_3269_);
lean_dec_ref(v_k_3269_);
v_res_3274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3268_, v_k_boxed_3273_, v_v_3270_, v_t_3271_, v_hl_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_3275_, lean_object* v_macroStack_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_3275_, v_macroStack_3276_, v___y_3281_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_3285_, lean_object* v_macroStack_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3285_, v_macroStack_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object* v_00_u03b2_3295_, uint64_t v_k_3296_, lean_object* v_t_3297_, lean_object* v_h_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3296_, v_t_3297_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object* v_00_u03b2_3300_, lean_object* v_k_3301_, lean_object* v_t_3302_, lean_object* v_h_3303_){
_start:
{
uint64_t v_k_boxed_3304_; lean_object* v_res_3305_; 
v_k_boxed_3304_ = lean_unbox_uint64(v_k_3301_);
lean_dec_ref(v_k_3301_);
v_res_3305_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_3300_, v_k_boxed_3304_, v_t_3302_, v_h_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3306_, lean_object* v_m_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3307_, v_a_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3310_, lean_object* v_m_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3310_, v_m_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_m_3311_);
return v_res_3313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object* v_00_u03b2_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_3315_, v_x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
uint8_t v_res_3321_; lean_object* v_r_3322_; 
v_res_3321_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_3318_, v_x_3319_, v_x_3320_);
lean_dec_ref(v_x_3320_);
lean_dec_ref(v_x_3319_);
v_r_3322_ = lean_box(v_res_3321_);
return v_r_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object* v_00_u03b2_3323_, lean_object* v_m_3324_, lean_object* v_query_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_m_3324_, v_query_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_m_3328_, lean_object* v_query_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_3327_, v_m_3328_, v_query_3329_);
lean_dec(v_query_3329_);
lean_dec_ref(v_m_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object* v_00_u03b2_3331_, lean_object* v_x_3332_, size_t v_x_3333_, lean_object* v_x_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_3332_, v_x_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object* v_00_u03b2_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_){
_start:
{
size_t v_x_35517__boxed_3340_; uint8_t v_res_3341_; lean_object* v_r_3342_; 
v_x_35517__boxed_3340_ = lean_unbox_usize(v_x_3338_);
lean_dec(v_x_3338_);
v_res_3341_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_3336_, v_x_3337_, v_x_35517__boxed_3340_, v_x_3339_);
lean_dec_ref(v_x_3339_);
lean_dec_ref(v_x_3337_);
v_r_3342_ = lean_box(v_res_3341_);
return v_r_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28(lean_object* v_00_u03b2_3343_, lean_object* v_m_3344_, lean_object* v_query_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___redArg(v_m_3344_, v_query_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28___boxed(lean_object* v_00_u03b2_3347_, lean_object* v_m_3348_, lean_object* v_query_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28(v_00_u03b2_3347_, v_m_3348_, v_query_3349_);
lean_dec(v_query_3349_);
lean_dec_ref(v_m_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object* v_00_u03b2_3351_, lean_object* v_keys_3352_, lean_object* v_vals_3353_, lean_object* v_heq_3354_, lean_object* v_i_3355_, lean_object* v_k_3356_){
_start:
{
uint8_t v___x_3357_; 
v___x_3357_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_3352_, v_i_3355_, v_k_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object* v_00_u03b2_3358_, lean_object* v_keys_3359_, lean_object* v_vals_3360_, lean_object* v_heq_3361_, lean_object* v_i_3362_, lean_object* v_k_3363_){
_start:
{
uint8_t v_res_3364_; lean_object* v_r_3365_; 
v_res_3364_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_3358_, v_keys_3359_, v_vals_3360_, v_heq_3361_, v_i_3362_, v_k_3363_);
lean_dec_ref(v_k_3363_);
lean_dec_ref(v_vals_3360_);
lean_dec_ref(v_keys_3359_);
v_r_3365_ = lean_box(v_res_3364_);
return v_r_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31(lean_object* v_00_u03b2_3366_, lean_object* v_m_3367_, lean_object* v_query_3368_, lean_object* v_x_3369_, lean_object* v_x_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___redArg(v_m_3367_, v_query_3368_, v_x_3369_, v_x_3370_, v_x_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31___boxed(lean_object* v_00_u03b2_3374_, lean_object* v_m_3375_, lean_object* v_query_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_, lean_object* v_x_3379_, lean_object* v_x_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18_spec__28_spec__31(v_00_u03b2_3374_, v_m_3375_, v_query_3376_, v_x_3377_, v_x_3378_, v_x_3379_, v_x_3380_);
lean_dec(v_query_3376_);
lean_dec_ref(v_m_3375_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3399_, lean_object* v_x_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3399_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___x_3410_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3409_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; uint64_t v_javascriptHash_3412_; lean_object* v_props_3413_; lean_object* v___x_3414_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v_javascriptHash_3412_ = lean_ctor_get_uint64(v_a_3411_, sizeof(void*)*2);
v_props_3413_ = lean_ctor_get(v_a_3411_, 1);
lean_inc_ref(v_props_3413_);
lean_dec(v_a_3411_);
v___x_3414_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3412_, v_props_3413_, v_x_3400_, v___y_3405_, v___y_3406_);
return v___x_3414_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_x_3400_);
v_a_3415_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3410_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3410_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_x_3400_);
v_a_3423_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3408_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3408_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3431_, lean_object* v_x_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3431_, v_x_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3441_);
v___x_3446_ = l_Lean_Syntax_isOfKind(v_x_3441_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec(v_x_3441_);
v___x_3447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3447_;
}
else
{
lean_object* v___x_3448_; lean_object* v_s_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; 
v___x_3448_ = lean_unsigned_to_nat(1u);
v_s_3449_ = l_Lean_Syntax_getArg(v_x_3441_, v___x_3448_);
v___f_3450_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3450_, 0, v_s_3449_);
lean_closure_set(v___f_3450_, 1, v_x_3441_);
v___x_3451_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3450_, v_a_3442_, v_a_3443_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Widget_elabWidgetCmd(v_x_3452_, v_a_3453_, v_a_3454_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
return v_res_3456_;
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
