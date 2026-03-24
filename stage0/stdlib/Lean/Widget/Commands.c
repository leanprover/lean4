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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__22___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(lean_object* v_mod_219_, lean_object* v_props_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_ref_228_; lean_object* v_quotContext_229_; lean_object* v_currMacroScope_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; 
v_ref_228_ = lean_ctor_get(v_a_225_, 5);
v_quotContext_229_ = lean_ctor_get(v_a_225_, 10);
v_currMacroScope_230_ = lean_ctor_get(v_a_225_, 11);
v___x_231_ = 0;
v___x_232_ = l_Lean_SourceInfo_fromRef(v_ref_228_, v___x_231_);
v___x_233_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3));
v___x_234_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4));
lean_inc(v___x_232_);
v___x_235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_237_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
lean_inc(v___x_232_);
v___x_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_232_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9));
v___x_240_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11));
v___x_241_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13));
v___x_242_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15);
v___x_243_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16));
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_244_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_243_, v_currMacroScope_230_);
v___x_245_ = lean_box(0);
v___x_246_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18));
lean_inc(v___x_232_);
v___x_247_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_247_, 0, v___x_232_);
lean_ctor_set(v___x_247_, 1, v___x_242_);
lean_ctor_set(v___x_247_, 2, v___x_244_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
lean_inc_ref(v___x_238_);
lean_inc(v___x_232_);
v___x_248_ = l_Lean_Syntax_node2(v___x_232_, v___x_241_, v___x_247_, v___x_238_);
v___x_249_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20));
v___x_250_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21));
lean_inc(v___x_232_);
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_232_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_TSyntax_getId(v_mod_219_);
v___x_253_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_252_);
lean_inc_ref(v___x_238_);
lean_inc_ref(v___x_251_);
lean_inc(v___x_232_);
v___x_254_ = l_Lean_Syntax_node3(v___x_232_, v___x_249_, v___x_251_, v___x_238_, v___x_253_);
lean_inc_ref_n(v___x_238_, 2);
lean_inc(v___x_232_);
v___x_255_ = l_Lean_Syntax_node3(v___x_232_, v___x_236_, v___x_238_, v___x_238_, v___x_254_);
lean_inc(v___x_232_);
v___x_256_ = l_Lean_Syntax_node2(v___x_232_, v___x_240_, v___x_248_, v___x_255_);
v___x_257_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23);
v___x_258_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24));
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_259_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_258_, v_currMacroScope_230_);
lean_inc(v___x_232_);
v___x_260_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_260_, 0, v___x_232_);
lean_ctor_set(v___x_260_, 1, v___x_257_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
lean_ctor_set(v___x_260_, 3, v___x_245_);
lean_inc_ref(v___x_238_);
lean_inc_ref(v___x_260_);
lean_inc(v___x_232_);
v___x_261_ = l_Lean_Syntax_node2(v___x_232_, v___x_241_, v___x_260_, v___x_238_);
v___x_262_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26));
v___x_263_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28));
v___x_264_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30));
v___x_265_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31));
lean_inc(v___x_232_);
v___x_266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_232_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33));
v___x_268_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35);
v___x_269_ = lean_box(0);
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_270_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_269_, v_currMacroScope_230_);
v___x_271_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46));
lean_inc(v___x_232_);
v___x_272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_272_, 0, v___x_232_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
lean_ctor_set(v___x_272_, 2, v___x_270_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
lean_inc(v___x_232_);
v___x_273_ = l_Lean_Syntax_node1(v___x_232_, v___x_267_, v___x_272_);
lean_inc(v___x_232_);
v___x_274_ = l_Lean_Syntax_node2(v___x_232_, v___x_264_, v___x_266_, v___x_273_);
v___x_275_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_276_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_277_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_278_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_277_, v_currMacroScope_230_);
v___x_279_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc(v___x_232_);
v___x_280_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_280_, 0, v___x_232_);
lean_ctor_set(v___x_280_, 1, v___x_276_);
lean_ctor_set(v___x_280_, 2, v___x_278_);
lean_ctor_set(v___x_280_, 3, v___x_279_);
lean_inc(v___x_232_);
v___x_281_ = l_Lean_Syntax_node1(v___x_232_, v___x_236_, v_mod_219_);
lean_inc(v___x_232_);
v___x_282_ = l_Lean_Syntax_node2(v___x_232_, v___x_275_, v___x_280_, v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57));
lean_inc(v___x_232_);
v___x_284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_232_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
lean_inc(v___x_232_);
v___x_285_ = l_Lean_Syntax_node3(v___x_232_, v___x_263_, v___x_274_, v___x_282_, v___x_284_);
v___x_286_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58));
lean_inc(v___x_232_);
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_232_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_inc(v___x_232_);
v___x_288_ = l_Lean_Syntax_node3(v___x_232_, v___x_262_, v___x_285_, v___x_287_, v___x_260_);
lean_inc_ref(v___x_238_);
lean_inc_ref(v___x_251_);
lean_inc(v___x_232_);
v___x_289_ = l_Lean_Syntax_node3(v___x_232_, v___x_249_, v___x_251_, v___x_238_, v___x_288_);
lean_inc_ref_n(v___x_238_, 2);
lean_inc(v___x_232_);
v___x_290_ = l_Lean_Syntax_node3(v___x_232_, v___x_236_, v___x_238_, v___x_238_, v___x_289_);
lean_inc(v___x_232_);
v___x_291_ = l_Lean_Syntax_node2(v___x_232_, v___x_240_, v___x_261_, v___x_290_);
v___x_292_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60);
v___x_293_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61));
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_294_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_293_, v_currMacroScope_230_);
lean_inc(v___x_232_);
v___x_295_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_295_, 0, v___x_232_);
lean_ctor_set(v___x_295_, 1, v___x_292_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
lean_ctor_set(v___x_295_, 3, v___x_245_);
lean_inc_ref(v___x_238_);
lean_inc(v___x_232_);
v___x_296_ = l_Lean_Syntax_node2(v___x_232_, v___x_241_, v___x_295_, v___x_238_);
v___x_297_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63);
v___x_298_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67));
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_299_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_298_, v_currMacroScope_230_);
v___x_300_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70));
lean_inc(v___x_232_);
v___x_301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_301_, 0, v___x_232_);
lean_ctor_set(v___x_301_, 1, v___x_297_);
lean_ctor_set(v___x_301_, 2, v___x_299_);
lean_ctor_set(v___x_301_, 3, v___x_300_);
lean_inc(v___x_232_);
v___x_302_ = l_Lean_Syntax_node1(v___x_232_, v___x_236_, v_props_220_);
lean_inc(v___x_232_);
v___x_303_ = l_Lean_Syntax_node2(v___x_232_, v___x_275_, v___x_301_, v___x_302_);
lean_inc_ref(v___x_238_);
lean_inc(v___x_232_);
v___x_304_ = l_Lean_Syntax_node3(v___x_232_, v___x_249_, v___x_251_, v___x_238_, v___x_303_);
lean_inc_ref_n(v___x_238_, 2);
lean_inc(v___x_232_);
v___x_305_ = l_Lean_Syntax_node3(v___x_232_, v___x_236_, v___x_238_, v___x_238_, v___x_304_);
lean_inc(v___x_232_);
v___x_306_ = l_Lean_Syntax_node2(v___x_232_, v___x_240_, v___x_296_, v___x_305_);
lean_inc_ref_n(v___x_238_, 2);
lean_inc(v___x_232_);
v___x_307_ = l_Lean_Syntax_node5(v___x_232_, v___x_236_, v___x_256_, v___x_238_, v___x_291_, v___x_238_, v___x_306_);
lean_inc(v___x_232_);
v___x_308_ = l_Lean_Syntax_node1(v___x_232_, v___x_239_, v___x_307_);
v___x_309_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72));
lean_inc_ref(v___x_238_);
lean_inc(v___x_232_);
v___x_310_ = l_Lean_Syntax_node1(v___x_232_, v___x_309_, v___x_238_);
v___x_311_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73));
lean_inc(v___x_232_);
v___x_312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_232_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
lean_inc_ref(v___x_238_);
v___x_313_ = l_Lean_Syntax_node6(v___x_232_, v___x_233_, v___x_235_, v___x_238_, v___x_308_, v___x_310_, v___x_238_, v___x_312_);
v___x_314_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77);
v___x_315_ = 1;
v___x_316_ = l_Lean_Elab_Term_elabTerm(v___x_313_, v___x_314_, v___x_315_, v___x_315_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___boxed(lean_object* v_mod_317_, lean_object* v_props_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_317_, v_props_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_box(0);
v___x_328_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg(){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___boxed(lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(lean_object* v_00_u03b1_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___boxed(lean_object* v_00_u03b1_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(v_00_u03b1_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__0));
v___x_355_ = l_String_toRawSubstring_x27(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v_x_376_);
v___x_385_ = l_Lean_Syntax_isOfKind(v_x_376_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_x_376_);
v___x_386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v_mod_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v_mod_388_ = l_Lean_Syntax_getArg(v_x_376_, v___x_387_);
v___x_389_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v_mod_388_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_mod_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec(v_mod_388_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_x_376_);
v___x_391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = l_Lean_Syntax_getArg(v_x_376_, v___x_392_);
lean_dec(v_x_376_);
lean_inc(v___x_393_);
v___x_394_ = l_Lean_Syntax_matchesNull(v___x_393_, v___x_387_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_393_);
v___x_396_ = l_Lean_Syntax_matchesNull(v___x_393_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec(v___x_393_);
lean_dec(v_mod_388_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
v___x_397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_397_;
}
else
{
lean_object* v_props_398_; lean_object* v___x_399_; 
v_props_398_ = l_Lean_Syntax_getArg(v___x_393_, v___x_392_);
lean_dec(v___x_393_);
v___x_399_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_388_, v_props_398_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_399_;
}
}
else
{
lean_object* v_ref_400_; lean_object* v_quotContext_401_; lean_object* v_currMacroScope_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_393_);
v_ref_400_ = lean_ctor_get(v_a_381_, 5);
v_quotContext_401_ = lean_ctor_get(v_a_381_, 10);
v_currMacroScope_402_ = lean_ctor_get(v_a_381_, 11);
v___x_403_ = 0;
v___x_404_ = l_Lean_SourceInfo_fromRef(v_ref_400_, v___x_403_);
v___x_405_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_406_ = lean_obj_once(&l_Lean_Widget_elabWidgetInstanceSpec___closed__1, &l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once, _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1);
v___x_407_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__4));
lean_inc(v_currMacroScope_402_);
lean_inc(v_quotContext_401_);
v___x_408_ = l_Lean_addMacroScope(v_quotContext_401_, v___x_407_, v_currMacroScope_402_);
v___x_409_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__7));
lean_inc(v___x_404_);
v___x_410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_410_, 0, v___x_404_);
lean_ctor_set(v___x_410_, 1, v___x_406_);
lean_ctor_set(v___x_410_, 2, v___x_408_);
lean_ctor_set(v___x_410_, 3, v___x_409_);
v___x_411_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_412_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__9));
v___x_413_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__10));
lean_inc(v___x_404_);
v___x_414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_404_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
lean_inc(v___x_404_);
v___x_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_404_);
lean_ctor_set(v___x_416_, 1, v___x_411_);
lean_ctor_set(v___x_416_, 2, v___x_415_);
v___x_417_ = ((lean_object*)(l_Lean_Widget_elabWidgetInstanceSpec___closed__11));
lean_inc(v___x_404_);
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_404_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
lean_inc(v___x_404_);
v___x_419_ = l_Lean_Syntax_node3(v___x_404_, v___x_412_, v___x_414_, v___x_416_, v___x_418_);
lean_inc(v___x_404_);
v___x_420_ = l_Lean_Syntax_node1(v___x_404_, v___x_411_, v___x_419_);
v___x_421_ = l_Lean_Syntax_node2(v___x_404_, v___x_405_, v___x_410_, v___x_420_);
v___x_422_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(v_mod_388_, v___x_421_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetInstanceSpec___boxed(lean_object* v_x_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Widget_elabWidgetInstanceSpec(v_x_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg___boxed(lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(lean_object* v_00_u03b1_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___boxed(lean_object* v_00_u03b1_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(v_00_u03b1_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(lean_object* v_e_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_Expr_hasMVar(v_e_540_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_e_540_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v_mctx_546_; lean_object* v___x_547_; lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_550_; lean_object* v_cache_551_; lean_object* v_zetaDeltaFVarIds_552_; lean_object* v_postponed_553_; lean_object* v_diag_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
v___x_545_ = lean_st_ref_get(v___y_541_);
v_mctx_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref(v_mctx_546_);
lean_dec(v___x_545_);
v___x_547_ = l_Lean_instantiateMVarsCore(v_mctx_546_, v_e_540_);
v_fst_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_fst_548_);
v_snd_549_ = lean_ctor_get(v___x_547_, 1);
lean_inc(v_snd_549_);
lean_dec_ref(v___x_547_);
v___x_550_ = lean_st_ref_take(v___y_541_);
v_cache_551_ = lean_ctor_get(v___x_550_, 1);
v_zetaDeltaFVarIds_552_ = lean_ctor_get(v___x_550_, 2);
v_postponed_553_ = lean_ctor_get(v___x_550_, 3);
v_diag_554_ = lean_ctor_get(v___x_550_, 4);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_550_, 0);
lean_dec(v_unused_564_);
v___x_556_ = v___x_550_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_diag_554_);
lean_inc(v_postponed_553_);
lean_inc(v_zetaDeltaFVarIds_552_);
lean_inc(v_cache_551_);
lean_dec(v___x_550_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_snd_549_);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_snd_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_cache_551_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_zetaDeltaFVarIds_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_postponed_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_diag_554_);
v___x_559_ = v_reuseFailAlloc_562_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_st_ref_set(v___y_541_, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_fst_548_);
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(lean_object* v_e_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_565_, v___y_566_);
lean_dec(v___y_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(lean_object* v_e_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_569_, v___y_573_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(lean_object* v_e_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(v_e_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(uint64_t v_k_587_, lean_object* v_t_588_){
_start:
{
if (lean_obj_tag(v_t_588_) == 0)
{
lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_l_591_; lean_object* v_r_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_1249_; 
v_k_589_ = lean_ctor_get(v_t_588_, 1);
v_v_590_ = lean_ctor_get(v_t_588_, 2);
v_l_591_ = lean_ctor_get(v_t_588_, 3);
v_r_592_ = lean_ctor_get(v_t_588_, 4);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_t_588_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_t_588_, 0);
lean_dec(v_unused_1250_);
v___x_594_ = v_t_588_;
v_isShared_595_ = v_isSharedCheck_1249_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_r_592_);
lean_inc(v_l_591_);
lean_inc(v_v_590_);
lean_inc(v_k_589_);
lean_dec(v_t_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_1249_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
uint64_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unbox_uint64(v_k_589_);
v___x_597_ = lean_uint64_dec_lt(v_k_587_, v___x_596_);
if (v___x_597_ == 0)
{
uint64_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unbox_uint64(v_k_589_);
v___x_599_ = lean_uint64_dec_eq(v_k_587_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v_impl_600_; lean_object* v___x_601_; 
v_impl_600_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_587_, v_r_592_);
v___x_601_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_600_) == 0)
{
if (lean_obj_tag(v_l_591_) == 0)
{
lean_object* v_size_602_; lean_object* v_size_603_; lean_object* v_k_604_; lean_object* v_v_605_; lean_object* v_l_606_; lean_object* v_r_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_size_602_ = lean_ctor_get(v_impl_600_, 0);
lean_inc(v_size_602_);
v_size_603_ = lean_ctor_get(v_l_591_, 0);
v_k_604_ = lean_ctor_get(v_l_591_, 1);
v_v_605_ = lean_ctor_get(v_l_591_, 2);
v_l_606_ = lean_ctor_get(v_l_591_, 3);
v_r_607_ = lean_ctor_get(v_l_591_, 4);
lean_inc(v_r_607_);
v___x_608_ = lean_unsigned_to_nat(3u);
v___x_609_ = lean_nat_mul(v___x_608_, v_size_602_);
v___x_610_ = lean_nat_dec_lt(v___x_609_, v_size_603_);
lean_dec(v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
lean_dec(v_r_607_);
v___x_611_ = lean_nat_add(v___x_601_, v_size_603_);
v___x_612_ = lean_nat_add(v___x_611_, v_size_602_);
lean_dec(v_size_602_);
lean_dec(v___x_611_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_impl_600_);
lean_ctor_set(v___x_594_, 0, v___x_612_);
v___x_614_ = v___x_594_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_impl_600_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_681_; 
lean_inc(v_l_606_);
lean_inc(v_v_605_);
lean_inc(v_k_604_);
lean_inc(v_size_603_);
v_isSharedCheck_681_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; lean_object* v_unused_686_; 
v_unused_682_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_l_591_, 2);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_l_591_, 1);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_686_);
v___x_617_ = v_l_591_;
v_isShared_618_ = v_isSharedCheck_681_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_l_591_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_681_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_size_619_; lean_object* v_size_620_; lean_object* v_k_621_; lean_object* v_v_622_; lean_object* v_l_623_; lean_object* v_r_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_size_619_ = lean_ctor_get(v_l_606_, 0);
v_size_620_ = lean_ctor_get(v_r_607_, 0);
v_k_621_ = lean_ctor_get(v_r_607_, 1);
v_v_622_ = lean_ctor_get(v_r_607_, 2);
v_l_623_ = lean_ctor_get(v_r_607_, 3);
v_r_624_ = lean_ctor_get(v_r_607_, 4);
v___x_625_ = lean_unsigned_to_nat(2u);
v___x_626_ = lean_nat_mul(v___x_625_, v_size_619_);
v___x_627_ = lean_nat_dec_lt(v_size_620_, v___x_626_);
lean_dec(v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_656_; 
lean_inc(v_r_624_);
lean_inc(v_l_623_);
lean_inc(v_v_622_);
lean_inc(v_k_621_);
v_isSharedCheck_656_ = !lean_is_exclusive(v_r_607_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; lean_object* v_unused_658_; lean_object* v_unused_659_; lean_object* v_unused_660_; lean_object* v_unused_661_; 
v_unused_657_ = lean_ctor_get(v_r_607_, 4);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_r_607_, 3);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_r_607_, 2);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_r_607_, 1);
lean_dec(v_unused_660_);
v_unused_661_ = lean_ctor_get(v_r_607_, 0);
lean_dec(v_unused_661_);
v___x_629_ = v_r_607_;
v_isShared_630_ = v_isSharedCheck_656_;
goto v_resetjp_628_;
}
else
{
lean_dec(v_r_607_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_656_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___x_644_; lean_object* v___y_646_; 
v___x_631_ = lean_nat_add(v___x_601_, v_size_603_);
lean_dec(v_size_603_);
v___x_632_ = lean_nat_add(v___x_631_, v_size_602_);
lean_dec(v___x_631_);
v___x_644_ = lean_nat_add(v___x_601_, v_size_619_);
if (lean_obj_tag(v_l_623_) == 0)
{
lean_object* v_size_654_; 
v_size_654_ = lean_ctor_get(v_l_623_, 0);
lean_inc(v_size_654_);
v___y_646_ = v_size_654_;
goto v___jp_645_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___y_646_ = v___x_655_;
goto v___jp_645_;
}
v___jp_633_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_nat_add(v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 4, v_impl_600_);
lean_ctor_set(v___x_629_, 3, v_r_624_);
lean_ctor_set(v___x_629_, 2, v_v_590_);
lean_ctor_set(v___x_629_, 1, v_k_589_);
lean_ctor_set(v___x_629_, 0, v___x_637_);
v___x_639_ = v___x_629_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_r_624_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_impl_600_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_639_);
lean_ctor_set(v___x_617_, 3, v___y_634_);
lean_ctor_set(v___x_617_, 2, v_v_622_);
lean_ctor_set(v___x_617_, 1, v_k_621_);
lean_ctor_set(v___x_617_, 0, v___x_632_);
v___x_641_ = v___x_617_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___y_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_nat_add(v___x_644_, v___y_646_);
lean_dec(v___y_646_);
lean_dec(v___x_644_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_l_623_);
lean_ctor_set(v___x_594_, 3, v_l_606_);
lean_ctor_set(v___x_594_, 2, v_v_605_);
lean_ctor_set(v___x_594_, 1, v_k_604_);
lean_ctor_set(v___x_594_, 0, v___x_647_);
v___x_649_ = v___x_594_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_k_604_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_v_605_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_l_606_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_l_623_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = lean_nat_add(v___x_601_, v_size_602_);
lean_dec(v_size_602_);
if (lean_obj_tag(v_r_624_) == 0)
{
lean_object* v_size_651_; 
v_size_651_ = lean_ctor_get(v_r_624_, 0);
lean_inc(v_size_651_);
v___y_634_ = v___x_649_;
v___y_635_ = v___x_650_;
v___y_636_ = v_size_651_;
goto v___jp_633_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___y_634_ = v___x_649_;
v___y_635_ = v___x_650_;
v___y_636_ = v___x_652_;
goto v___jp_633_;
}
}
}
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_del_object(v___x_594_);
v___x_662_ = lean_nat_add(v___x_601_, v_size_603_);
lean_dec(v_size_603_);
v___x_663_ = lean_nat_add(v___x_662_, v_size_602_);
lean_dec(v___x_662_);
v___x_664_ = lean_nat_add(v___x_601_, v_size_602_);
lean_dec(v_size_602_);
v___x_665_ = lean_nat_add(v___x_664_, v_size_620_);
lean_dec(v___x_664_);
lean_inc_ref(v_impl_600_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_impl_600_);
lean_ctor_set(v___x_617_, 3, v_r_607_);
lean_ctor_set(v___x_617_, 2, v_v_590_);
lean_ctor_set(v___x_617_, 1, v_k_589_);
lean_ctor_set(v___x_617_, 0, v___x_665_);
v___x_667_ = v___x_617_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_r_607_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_impl_600_);
v___x_667_ = v_reuseFailAlloc_680_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_isSharedCheck_674_ = !lean_is_exclusive(v_impl_600_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; lean_object* v_unused_679_; 
v_unused_675_ = lean_ctor_get(v_impl_600_, 4);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_impl_600_, 3);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_impl_600_, 2);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_impl_600_, 1);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_impl_600_, 0);
lean_dec(v_unused_679_);
v___x_669_ = v_impl_600_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_impl_600_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v___x_667_);
lean_ctor_set(v___x_669_, 3, v_l_606_);
lean_ctor_set(v___x_669_, 2, v_v_605_);
lean_ctor_set(v___x_669_, 1, v_k_604_);
lean_ctor_set(v___x_669_, 0, v___x_663_);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_k_604_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_v_605_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_l_606_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v___x_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_size_687_ = lean_ctor_get(v_impl_600_, 0);
lean_inc(v_size_687_);
v___x_688_ = lean_nat_add(v___x_601_, v_size_687_);
lean_dec(v_size_687_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_impl_600_);
lean_ctor_set(v___x_594_, 0, v___x_688_);
v___x_690_ = v___x_594_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_impl_600_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
if (lean_obj_tag(v_l_591_) == 0)
{
lean_object* v_l_692_; 
v_l_692_ = lean_ctor_get(v_l_591_, 3);
if (lean_obj_tag(v_l_692_) == 0)
{
lean_object* v_r_693_; 
lean_inc_ref(v_l_692_);
v_r_693_ = lean_ctor_get(v_l_591_, 4);
lean_inc(v_r_693_);
if (lean_obj_tag(v_r_693_) == 0)
{
lean_object* v_size_694_; lean_object* v_k_695_; lean_object* v_v_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_709_; 
v_size_694_ = lean_ctor_get(v_l_591_, 0);
v_k_695_ = lean_ctor_get(v_l_591_, 1);
v_v_696_ = lean_ctor_get(v_l_591_, 2);
v_isSharedCheck_709_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_710_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_711_);
v___x_698_ = v_l_591_;
v_isShared_699_ = v_isSharedCheck_709_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_v_696_);
lean_inc(v_k_695_);
lean_inc(v_size_694_);
lean_dec(v_l_591_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_709_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_size_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_size_700_ = lean_ctor_get(v_r_693_, 0);
v___x_701_ = lean_nat_add(v___x_601_, v_size_694_);
lean_dec(v_size_694_);
v___x_702_ = lean_nat_add(v___x_601_, v_size_700_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 4, v_impl_600_);
lean_ctor_set(v___x_698_, 3, v_r_693_);
lean_ctor_set(v___x_698_, 2, v_v_590_);
lean_ctor_set(v___x_698_, 1, v_k_589_);
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_impl_600_);
v___x_704_ = v_reuseFailAlloc_708_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_704_);
lean_ctor_set(v___x_594_, 3, v_l_692_);
lean_ctor_set(v___x_594_, 2, v_v_696_);
lean_ctor_set(v___x_594_, 1, v_k_695_);
lean_ctor_set(v___x_594_, 0, v___x_701_);
v___x_706_ = v___x_594_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_k_712_; lean_object* v_v_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_724_; 
v_k_712_ = lean_ctor_get(v_l_591_, 1);
v_v_713_ = lean_ctor_get(v_l_591_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; 
v_unused_725_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_727_);
v___x_715_ = v_l_591_;
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_v_713_);
lean_inc(v_k_712_);
lean_dec(v_l_591_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(3u);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 3, v_r_693_);
lean_ctor_set(v___x_715_, 2, v_v_590_);
lean_ctor_set(v___x_715_, 1, v_k_589_);
lean_ctor_set(v___x_715_, 0, v___x_601_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_r_693_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_719_);
lean_ctor_set(v___x_594_, 3, v_l_692_);
lean_ctor_set(v___x_594_, 2, v_v_713_);
lean_ctor_set(v___x_594_, 1, v_k_712_);
lean_ctor_set(v___x_594_, 0, v___x_717_);
v___x_721_ = v___x_594_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
else
{
lean_object* v_r_728_; 
v_r_728_ = lean_ctor_get(v_l_591_, 4);
lean_inc(v_r_728_);
if (lean_obj_tag(v_r_728_) == 0)
{
lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_753_; 
lean_inc(v_l_692_);
v_k_729_ = lean_ctor_get(v_l_591_, 1);
v_v_730_ = lean_ctor_get(v_l_591_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; lean_object* v_unused_755_; lean_object* v_unused_756_; 
v_unused_754_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_756_);
v___x_732_ = v_l_591_;
v_isShared_733_ = v_isSharedCheck_753_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_v_730_);
lean_inc(v_k_729_);
lean_dec(v_l_591_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_753_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_k_734_; lean_object* v_v_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_749_; 
v_k_734_ = lean_ctor_get(v_r_728_, 1);
v_v_735_ = lean_ctor_get(v_r_728_, 2);
v_isSharedCheck_749_ = !lean_is_exclusive(v_r_728_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; 
v_unused_750_ = lean_ctor_get(v_r_728_, 4);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_r_728_, 3);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_r_728_, 0);
lean_dec(v_unused_752_);
v___x_737_ = v_r_728_;
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_v_735_);
lean_inc(v_k_734_);
lean_dec(v_r_728_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(3u);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 4, v_l_692_);
lean_ctor_set(v___x_737_, 3, v_l_692_);
lean_ctor_set(v___x_737_, 2, v_v_730_);
lean_ctor_set(v___x_737_, 1, v_k_729_);
lean_ctor_set(v___x_737_, 0, v___x_601_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_729_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_730_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_l_692_);
v___x_741_ = v_reuseFailAlloc_748_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 4, v_l_692_);
lean_ctor_set(v___x_732_, 2, v_v_590_);
lean_ctor_set(v___x_732_, 1, v_k_589_);
lean_ctor_set(v___x_732_, 0, v___x_601_);
v___x_743_ = v___x_732_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_l_692_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_743_);
lean_ctor_set(v___x_594_, 3, v___x_741_);
lean_ctor_set(v___x_594_, 2, v_v_735_);
lean_ctor_set(v___x_594_, 1, v_k_734_);
lean_ctor_set(v___x_594_, 0, v___x_739_);
v___x_745_ = v___x_594_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_734_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v___x_741_);
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
}
else
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_unsigned_to_nat(2u);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_r_728_);
lean_ctor_set(v___x_594_, 0, v___x_757_);
v___x_759_ = v___x_594_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_r_728_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v___x_762_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_l_591_);
lean_ctor_set(v___x_594_, 0, v___x_601_);
v___x_762_ = v___x_594_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_l_591_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_del_object(v___x_594_);
lean_dec(v_v_590_);
lean_dec(v_k_589_);
if (lean_obj_tag(v_l_591_) == 0)
{
if (lean_obj_tag(v_r_592_) == 0)
{
lean_object* v_size_764_; lean_object* v_k_765_; lean_object* v_v_766_; lean_object* v_l_767_; lean_object* v_r_768_; lean_object* v_size_769_; lean_object* v_k_770_; lean_object* v_v_771_; lean_object* v_l_772_; lean_object* v_r_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_size_764_ = lean_ctor_get(v_l_591_, 0);
v_k_765_ = lean_ctor_get(v_l_591_, 1);
v_v_766_ = lean_ctor_get(v_l_591_, 2);
v_l_767_ = lean_ctor_get(v_l_591_, 3);
v_r_768_ = lean_ctor_get(v_l_591_, 4);
lean_inc(v_r_768_);
v_size_769_ = lean_ctor_get(v_r_592_, 0);
v_k_770_ = lean_ctor_get(v_r_592_, 1);
v_v_771_ = lean_ctor_get(v_r_592_, 2);
v_l_772_ = lean_ctor_get(v_r_592_, 3);
lean_inc(v_l_772_);
v_r_773_ = lean_ctor_get(v_r_592_, 4);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_dec_lt(v_size_764_, v_size_769_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_911_; 
lean_inc(v_l_767_);
lean_inc(v_v_766_);
lean_inc(v_k_765_);
v_isSharedCheck_911_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; lean_object* v_unused_913_; lean_object* v_unused_914_; lean_object* v_unused_915_; lean_object* v_unused_916_; 
v_unused_912_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_l_591_, 2);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_l_591_, 1);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_916_);
v___x_777_ = v_l_591_;
v_isShared_778_ = v_isSharedCheck_911_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_l_591_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_911_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v_tree_780_; 
v___x_779_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_765_, v_v_766_, v_l_767_, v_r_768_);
v_tree_780_ = lean_ctor_get(v___x_779_, 2);
lean_inc(v_tree_780_);
if (lean_obj_tag(v_tree_780_) == 0)
{
lean_object* v_k_781_; lean_object* v_v_782_; lean_object* v_size_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_k_781_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_k_781_);
v_v_782_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_v_782_);
lean_dec_ref(v___x_779_);
v_size_783_ = lean_ctor_get(v_tree_780_, 0);
v___x_784_ = lean_unsigned_to_nat(3u);
v___x_785_ = lean_nat_mul(v___x_784_, v_size_783_);
v___x_786_ = lean_nat_dec_lt(v___x_785_, v_size_769_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_dec(v_l_772_);
v___x_787_ = lean_nat_add(v___x_774_, v_size_783_);
v___x_788_ = lean_nat_add(v___x_787_, v_size_769_);
lean_dec(v___x_787_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_r_592_);
lean_ctor_set(v___x_777_, 3, v_tree_780_);
lean_ctor_set(v___x_777_, 2, v_v_782_);
lean_ctor_set(v___x_777_, 1, v_k_781_);
lean_ctor_set(v___x_777_, 0, v___x_788_);
v___x_790_ = v___x_777_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_tree_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_r_592_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_846_; 
lean_inc(v_r_773_);
lean_inc(v_v_771_);
lean_inc(v_k_770_);
lean_inc(v_size_769_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_847_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_r_592_, 2);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_r_592_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_851_);
v___x_793_ = v_r_592_;
v_isShared_794_ = v_isSharedCheck_846_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_r_592_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_846_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_size_795_; lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v_l_798_; lean_object* v_r_799_; lean_object* v_size_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_size_795_ = lean_ctor_get(v_l_772_, 0);
v_k_796_ = lean_ctor_get(v_l_772_, 1);
v_v_797_ = lean_ctor_get(v_l_772_, 2);
v_l_798_ = lean_ctor_get(v_l_772_, 3);
v_r_799_ = lean_ctor_get(v_l_772_, 4);
v_size_800_ = lean_ctor_get(v_r_773_, 0);
v___x_801_ = lean_unsigned_to_nat(2u);
v___x_802_ = lean_nat_mul(v___x_801_, v_size_800_);
v___x_803_ = lean_nat_dec_lt(v_size_795_, v___x_802_);
lean_dec(v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_831_; 
lean_inc(v_r_799_);
lean_inc(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_l_772_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_832_ = lean_ctor_get(v_l_772_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_l_772_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_l_772_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_l_772_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_l_772_, 0);
lean_dec(v_unused_836_);
v___x_805_ = v_l_772_;
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_l_772_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_821_; 
v___x_807_ = lean_nat_add(v___x_774_, v_size_783_);
v___x_808_ = lean_nat_add(v___x_807_, v_size_769_);
lean_dec(v_size_769_);
if (lean_obj_tag(v_l_798_) == 0)
{
lean_object* v_size_829_; 
v_size_829_ = lean_ctor_get(v_l_798_, 0);
lean_inc(v_size_829_);
v___y_821_ = v_size_829_;
goto v___jp_820_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
v___jp_809_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_nat_add(v___y_810_, v___y_812_);
lean_dec(v___y_812_);
lean_dec(v___y_810_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 4, v_r_773_);
lean_ctor_set(v___x_805_, 3, v_r_799_);
lean_ctor_set(v___x_805_, 2, v_v_771_);
lean_ctor_set(v___x_805_, 1, v_k_770_);
lean_ctor_set(v___x_805_, 0, v___x_813_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_r_799_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_r_773_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v___x_815_);
lean_ctor_set(v___x_793_, 3, v___y_811_);
lean_ctor_set(v___x_793_, 2, v_v_797_);
lean_ctor_set(v___x_793_, 1, v_k_796_);
lean_ctor_set(v___x_793_, 0, v___x_808_);
v___x_817_ = v___x_793_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___y_811_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_nat_add(v___x_807_, v___y_821_);
lean_dec(v___y_821_);
lean_dec(v___x_807_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_l_798_);
lean_ctor_set(v___x_777_, 3, v_tree_780_);
lean_ctor_set(v___x_777_, 2, v_v_782_);
lean_ctor_set(v___x_777_, 1, v_k_781_);
lean_ctor_set(v___x_777_, 0, v___x_822_);
v___x_824_ = v___x_777_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_tree_780_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_l_798_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_nat_add(v___x_774_, v_size_800_);
if (lean_obj_tag(v_r_799_) == 0)
{
lean_object* v_size_826_; 
v_size_826_ = lean_ctor_get(v_r_799_, 0);
lean_inc(v_size_826_);
v___y_810_ = v___x_825_;
v___y_811_ = v___x_824_;
v___y_812_ = v_size_826_;
goto v___jp_809_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___y_810_ = v___x_825_;
v___y_811_ = v___x_824_;
v___y_812_ = v___x_827_;
goto v___jp_809_;
}
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_837_ = lean_nat_add(v___x_774_, v_size_783_);
v___x_838_ = lean_nat_add(v___x_837_, v_size_769_);
lean_dec(v_size_769_);
v___x_839_ = lean_nat_add(v___x_837_, v_size_795_);
lean_dec(v___x_837_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v_l_772_);
lean_ctor_set(v___x_793_, 3, v_tree_780_);
lean_ctor_set(v___x_793_, 2, v_v_782_);
lean_ctor_set(v___x_793_, 1, v_k_781_);
lean_ctor_set(v___x_793_, 0, v___x_839_);
v___x_841_ = v___x_793_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_tree_780_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_l_772_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_r_773_);
lean_ctor_set(v___x_777_, 3, v___x_841_);
lean_ctor_set(v___x_777_, 2, v_v_771_);
lean_ctor_set(v___x_777_, 1, v_k_770_);
lean_ctor_set(v___x_777_, 0, v___x_838_);
v___x_843_ = v___x_777_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_r_773_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
else
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_905_; 
lean_inc(v_r_773_);
lean_inc(v_v_771_);
lean_inc(v_k_770_);
lean_inc(v_size_769_);
v_isSharedCheck_905_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; lean_object* v_unused_907_; lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; 
v_unused_906_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_r_592_, 2);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_r_592_, 1);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_910_);
v___x_853_ = v_r_592_;
v_isShared_854_ = v_isSharedCheck_905_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_r_592_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_905_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
if (lean_obj_tag(v_l_772_) == 0)
{
if (lean_obj_tag(v_r_773_) == 0)
{
lean_object* v_k_855_; lean_object* v_v_856_; lean_object* v_size_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v_k_855_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_k_855_);
v_v_856_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_v_856_);
lean_dec_ref(v___x_779_);
v_size_857_ = lean_ctor_get(v_l_772_, 0);
v___x_858_ = lean_nat_add(v___x_774_, v_size_769_);
lean_dec(v_size_769_);
v___x_859_ = lean_nat_add(v___x_774_, v_size_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 4, v_l_772_);
lean_ctor_set(v___x_853_, 3, v_tree_780_);
lean_ctor_set(v___x_853_, 2, v_v_856_);
lean_ctor_set(v___x_853_, 1, v_k_855_);
lean_ctor_set(v___x_853_, 0, v___x_859_);
v___x_861_ = v___x_853_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_tree_780_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_l_772_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_r_773_);
lean_ctor_set(v___x_777_, 3, v___x_861_);
lean_ctor_set(v___x_777_, 2, v_v_771_);
lean_ctor_set(v___x_777_, 1, v_k_770_);
lean_ctor_set(v___x_777_, 0, v___x_858_);
v___x_863_ = v___x_777_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 4, v_r_773_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_k_866_; lean_object* v_v_867_; lean_object* v_k_868_; lean_object* v_v_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_size_769_);
v_k_866_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_k_866_);
v_v_867_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_v_867_);
lean_dec_ref(v___x_779_);
v_k_868_ = lean_ctor_get(v_l_772_, 1);
v_v_869_ = lean_ctor_get(v_l_772_, 2);
v_isSharedCheck_883_ = !lean_is_exclusive(v_l_772_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; 
v_unused_884_ = lean_ctor_get(v_l_772_, 4);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_l_772_, 3);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_l_772_, 0);
lean_dec(v_unused_886_);
v___x_871_ = v_l_772_;
v_isShared_872_ = v_isSharedCheck_883_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_v_869_);
lean_inc(v_k_868_);
lean_dec(v_l_772_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_883_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_unsigned_to_nat(3u);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v_r_773_);
lean_ctor_set(v___x_871_, 3, v_r_773_);
lean_ctor_set(v___x_871_, 2, v_v_867_);
lean_ctor_set(v___x_871_, 1, v_k_866_);
lean_ctor_set(v___x_871_, 0, v___x_774_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_866_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_r_773_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_r_773_);
v___x_875_ = v_reuseFailAlloc_882_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 3, v_r_773_);
lean_ctor_set(v___x_853_, 0, v___x_774_);
v___x_877_ = v___x_853_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_r_773_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_r_773_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v___x_877_);
lean_ctor_set(v___x_777_, 3, v___x_875_);
lean_ctor_set(v___x_777_, 2, v_v_869_);
lean_ctor_set(v___x_777_, 1, v_k_868_);
lean_ctor_set(v___x_777_, 0, v___x_873_);
v___x_879_ = v___x_777_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_868_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_869_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_773_) == 0)
{
lean_object* v_k_887_; lean_object* v_v_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_size_769_);
v_k_887_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_k_887_);
v_v_888_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_v_888_);
lean_dec_ref(v___x_779_);
v___x_889_ = lean_unsigned_to_nat(3u);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 4, v_l_772_);
lean_ctor_set(v___x_853_, 2, v_v_888_);
lean_ctor_set(v___x_853_, 1, v_k_887_);
lean_ctor_set(v___x_853_, 0, v___x_774_);
v___x_891_ = v___x_853_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_l_772_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_l_772_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_r_773_);
lean_ctor_set(v___x_777_, 3, v___x_891_);
lean_ctor_set(v___x_777_, 2, v_v_771_);
lean_ctor_set(v___x_777_, 1, v_k_770_);
lean_ctor_set(v___x_777_, 0, v___x_889_);
v___x_893_ = v___x_777_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_r_773_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_k_896_; lean_object* v_v_897_; lean_object* v___x_899_; 
v_k_896_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_k_896_);
v_v_897_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_v_897_);
lean_dec_ref(v___x_779_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 3, v_r_773_);
v___x_899_ = v___x_853_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_size_769_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_r_773_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_773_);
v___x_899_ = v_reuseFailAlloc_904_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_unsigned_to_nat(2u);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v___x_899_);
lean_ctor_set(v___x_777_, 3, v_r_773_);
lean_ctor_set(v___x_777_, 2, v_v_897_);
lean_ctor_set(v___x_777_, 1, v_k_896_);
lean_ctor_set(v___x_777_, 0, v___x_900_);
v___x_902_ = v___x_777_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_896_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_897_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_r_773_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v___x_899_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
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
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1069_; 
lean_inc(v_r_773_);
lean_inc(v_v_771_);
lean_inc(v_k_770_);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; 
v_unused_1070_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_r_592_, 2);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_r_592_, 1);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_1074_);
v___x_918_ = v_r_592_;
v_isShared_919_ = v_isSharedCheck_1069_;
goto v_resetjp_917_;
}
else
{
lean_dec(v_r_592_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1069_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v_tree_921_; 
v___x_920_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_770_, v_v_771_, v_l_772_, v_r_773_);
v_tree_921_ = lean_ctor_get(v___x_920_, 2);
lean_inc(v_tree_921_);
if (lean_obj_tag(v_tree_921_) == 0)
{
lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v_size_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_k_922_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_k_922_);
v_v_923_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_v_923_);
lean_dec_ref(v___x_920_);
v_size_924_ = lean_ctor_get(v_tree_921_, 0);
v___x_925_ = lean_unsigned_to_nat(3u);
v___x_926_ = lean_nat_mul(v___x_925_, v_size_924_);
v___x_927_ = lean_nat_dec_lt(v___x_926_, v_size_764_);
lean_dec(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v_r_768_);
v___x_928_ = lean_nat_add(v___x_774_, v_size_764_);
v___x_929_ = lean_nat_add(v___x_928_, v_size_924_);
lean_dec(v___x_928_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_tree_921_);
lean_ctor_set(v___x_918_, 3, v_l_591_);
lean_ctor_set(v___x_918_, 2, v_v_923_);
lean_ctor_set(v___x_918_, 1, v_k_922_);
lean_ctor_set(v___x_918_, 0, v___x_929_);
v___x_931_ = v___x_918_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_922_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_923_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_tree_921_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_998_; 
lean_inc(v_l_767_);
lean_inc(v_v_766_);
lean_inc(v_k_765_);
lean_inc(v_size_764_);
v_isSharedCheck_998_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; lean_object* v_unused_1000_; lean_object* v_unused_1001_; lean_object* v_unused_1002_; lean_object* v_unused_1003_; 
v_unused_999_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_l_591_, 2);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_l_591_, 1);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_1003_);
v___x_934_ = v_l_591_;
v_isShared_935_ = v_isSharedCheck_998_;
goto v_resetjp_933_;
}
else
{
lean_dec(v_l_591_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_998_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_size_936_; lean_object* v_size_937_; lean_object* v_k_938_; lean_object* v_v_939_; lean_object* v_l_940_; lean_object* v_r_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_size_936_ = lean_ctor_get(v_l_767_, 0);
v_size_937_ = lean_ctor_get(v_r_768_, 0);
v_k_938_ = lean_ctor_get(v_r_768_, 1);
v_v_939_ = lean_ctor_get(v_r_768_, 2);
v_l_940_ = lean_ctor_get(v_r_768_, 3);
v_r_941_ = lean_ctor_get(v_r_768_, 4);
v___x_942_ = lean_unsigned_to_nat(2u);
v___x_943_ = lean_nat_mul(v___x_942_, v_size_936_);
v___x_944_ = lean_nat_dec_lt(v_size_937_, v___x_943_);
lean_dec(v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_982_; 
lean_inc(v_r_941_);
lean_inc(v_l_940_);
lean_inc(v_v_939_);
lean_inc(v_k_938_);
lean_del_object(v___x_934_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_r_768_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_983_ = lean_ctor_get(v_r_768_, 4);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_r_768_, 3);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_r_768_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_r_768_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_r_768_, 0);
lean_dec(v_unused_987_);
v___x_946_ = v_r_768_;
v_isShared_947_ = v_isSharedCheck_982_;
goto v_resetjp_945_;
}
else
{
lean_dec(v_r_768_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_982_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___x_970_; lean_object* v___y_972_; 
v___x_948_ = lean_nat_add(v___x_774_, v_size_764_);
lean_dec(v_size_764_);
v___x_949_ = lean_nat_add(v___x_948_, v_size_924_);
lean_dec(v___x_948_);
v___x_970_ = lean_nat_add(v___x_774_, v_size_936_);
if (lean_obj_tag(v_l_940_) == 0)
{
lean_object* v_size_980_; 
v_size_980_ = lean_ctor_get(v_l_940_, 0);
lean_inc(v_size_980_);
v___y_972_ = v_size_980_;
goto v___jp_971_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___y_972_ = v___x_981_;
goto v___jp_971_;
}
v___jp_950_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_nat_add(v___y_951_, v___y_953_);
lean_dec(v___y_953_);
lean_dec(v___y_951_);
lean_inc_ref(v_tree_921_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 4, v_tree_921_);
lean_ctor_set(v___x_946_, 3, v_r_941_);
lean_ctor_set(v___x_946_, 2, v_v_923_);
lean_ctor_set(v___x_946_, 1, v_k_922_);
lean_ctor_set(v___x_946_, 0, v___x_954_);
v___x_956_ = v___x_946_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_k_922_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_v_923_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_r_941_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_tree_921_);
v___x_956_ = v_reuseFailAlloc_969_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_isSharedCheck_963_ = !lean_is_exclusive(v_tree_921_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; lean_object* v_unused_965_; lean_object* v_unused_966_; lean_object* v_unused_967_; lean_object* v_unused_968_; 
v_unused_964_ = lean_ctor_get(v_tree_921_, 4);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_tree_921_, 3);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_tree_921_, 2);
lean_dec(v_unused_966_);
v_unused_967_ = lean_ctor_get(v_tree_921_, 1);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_tree_921_, 0);
lean_dec(v_unused_968_);
v___x_958_ = v_tree_921_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_dec(v_tree_921_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 4, v___x_956_);
lean_ctor_set(v___x_958_, 3, v___y_952_);
lean_ctor_set(v___x_958_, 2, v_v_939_);
lean_ctor_set(v___x_958_, 1, v_k_938_);
lean_ctor_set(v___x_958_, 0, v___x_949_);
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_k_938_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_v_939_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v___y_952_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v___x_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_nat_add(v___x_970_, v___y_972_);
lean_dec(v___y_972_);
lean_dec(v___x_970_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_l_940_);
lean_ctor_set(v___x_918_, 3, v_l_767_);
lean_ctor_set(v___x_918_, 2, v_v_766_);
lean_ctor_set(v___x_918_, 1, v_k_765_);
lean_ctor_set(v___x_918_, 0, v___x_973_);
v___x_975_ = v___x_918_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_l_940_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = lean_nat_add(v___x_774_, v_size_924_);
if (lean_obj_tag(v_r_941_) == 0)
{
lean_object* v_size_977_; 
v_size_977_ = lean_ctor_get(v_r_941_, 0);
lean_inc(v_size_977_);
v___y_951_ = v___x_976_;
v___y_952_ = v___x_975_;
v___y_953_ = v_size_977_;
goto v___jp_950_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___y_951_ = v___x_976_;
v___y_952_ = v___x_975_;
v___y_953_ = v___x_978_;
goto v___jp_950_;
}
}
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_988_ = lean_nat_add(v___x_774_, v_size_764_);
lean_dec(v_size_764_);
v___x_989_ = lean_nat_add(v___x_988_, v_size_924_);
lean_dec(v___x_988_);
v___x_990_ = lean_nat_add(v___x_774_, v_size_924_);
v___x_991_ = lean_nat_add(v___x_990_, v_size_937_);
lean_dec(v___x_990_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_tree_921_);
lean_ctor_set(v___x_918_, 3, v_r_768_);
lean_ctor_set(v___x_918_, 2, v_v_923_);
lean_ctor_set(v___x_918_, 1, v_k_922_);
lean_ctor_set(v___x_918_, 0, v___x_991_);
v___x_993_ = v___x_918_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_k_922_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_v_923_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_r_768_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_tree_921_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 4, v___x_993_);
lean_ctor_set(v___x_934_, 0, v___x_989_);
v___x_995_ = v___x_934_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_767_) == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1027_; 
lean_inc_ref(v_l_767_);
lean_inc(v_v_766_);
lean_inc(v_k_765_);
lean_inc(v_size_764_);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; lean_object* v_unused_1032_; 
v_unused_1028_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_l_591_, 2);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_l_591_, 1);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_1032_);
v___x_1005_ = v_l_591_;
v_isShared_1006_ = v_isSharedCheck_1027_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_l_591_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1027_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
if (lean_obj_tag(v_r_768_) == 0)
{
lean_object* v_k_1007_; lean_object* v_v_1008_; lean_object* v_size_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v_k_1007_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_k_1007_);
v_v_1008_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_v_1008_);
lean_dec_ref(v___x_920_);
v_size_1009_ = lean_ctor_get(v_r_768_, 0);
v___x_1010_ = lean_nat_add(v___x_774_, v_size_764_);
lean_dec(v_size_764_);
v___x_1011_ = lean_nat_add(v___x_774_, v_size_1009_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_tree_921_);
lean_ctor_set(v___x_918_, 3, v_r_768_);
lean_ctor_set(v___x_918_, 2, v_v_1008_);
lean_ctor_set(v___x_918_, 1, v_k_1007_);
lean_ctor_set(v___x_918_, 0, v___x_1011_);
v___x_1013_ = v___x_918_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_r_768_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_tree_921_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v___x_1013_);
lean_ctor_set(v___x_1005_, 0, v___x_1010_);
v___x_1015_ = v___x_1005_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_k_1018_; lean_object* v_v_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_dec(v_size_764_);
v_k_1018_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_k_1018_);
v_v_1019_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_v_1019_);
lean_dec_ref(v___x_920_);
v___x_1020_ = lean_unsigned_to_nat(3u);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_r_768_);
lean_ctor_set(v___x_918_, 3, v_r_768_);
lean_ctor_set(v___x_918_, 2, v_v_1019_);
lean_ctor_set(v___x_918_, 1, v_k_1018_);
lean_ctor_set(v___x_918_, 0, v___x_774_);
v___x_1022_ = v___x_918_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_k_1018_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_v_1019_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_r_768_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v_r_768_);
v___x_1022_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v___x_1022_);
lean_ctor_set(v___x_1005_, 0, v___x_1020_);
v___x_1024_ = v___x_1005_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_768_) == 0)
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1057_; 
lean_inc(v_l_767_);
lean_inc(v_v_766_);
lean_inc(v_k_765_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_l_591_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; 
v_unused_1058_ = lean_ctor_get(v_l_591_, 4);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_l_591_, 3);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_l_591_, 2);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_l_591_, 1);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_l_591_, 0);
lean_dec(v_unused_1062_);
v___x_1034_ = v_l_591_;
v_isShared_1035_ = v_isSharedCheck_1057_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_l_591_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1057_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_k_1036_; lean_object* v_v_1037_; lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1053_; 
v_k_1036_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_k_1036_);
v_v_1037_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_v_1037_);
lean_dec_ref(v___x_920_);
v_k_1038_ = lean_ctor_get(v_r_768_, 1);
v_v_1039_ = lean_ctor_get(v_r_768_, 2);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_r_768_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; lean_object* v_unused_1056_; 
v_unused_1054_ = lean_ctor_get(v_r_768_, 4);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_r_768_, 3);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_r_768_, 0);
lean_dec(v_unused_1056_);
v___x_1041_ = v_r_768_;
v_isShared_1042_ = v_isSharedCheck_1053_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_v_1039_);
lean_inc(v_k_1038_);
lean_dec(v_r_768_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1053_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_unsigned_to_nat(3u);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v_l_767_);
lean_ctor_set(v___x_1041_, 3, v_l_767_);
lean_ctor_set(v___x_1041_, 2, v_v_766_);
lean_ctor_set(v___x_1041_, 1, v_k_765_);
lean_ctor_set(v___x_1041_, 0, v___x_774_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_l_767_);
v___x_1045_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_l_767_);
lean_ctor_set(v___x_918_, 3, v_l_767_);
lean_ctor_set(v___x_918_, 2, v_v_1037_);
lean_ctor_set(v___x_918_, 1, v_k_1036_);
lean_ctor_set(v___x_918_, 0, v___x_774_);
v___x_1047_ = v___x_918_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_k_1036_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_v_1037_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_l_767_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v___x_1047_);
lean_ctor_set(v___x_1034_, 3, v___x_1045_);
lean_ctor_set(v___x_1034_, 2, v_v_1039_);
lean_ctor_set(v___x_1034_, 1, v_k_1038_);
lean_ctor_set(v___x_1034_, 0, v___x_1043_);
v___x_1049_ = v___x_1034_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
else
{
lean_object* v_k_1063_; lean_object* v_v_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v_k_1063_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_k_1063_);
v_v_1064_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_v_1064_);
lean_dec_ref(v___x_920_);
v___x_1065_ = lean_unsigned_to_nat(2u);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_r_768_);
lean_ctor_set(v___x_918_, 3, v_l_591_);
lean_ctor_set(v___x_918_, 2, v_v_1064_);
lean_ctor_set(v___x_918_, 1, v_k_1063_);
lean_ctor_set(v___x_918_, 0, v___x_1065_);
v___x_1067_ = v___x_918_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_k_1063_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_v_1064_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_r_768_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
}
else
{
return v_l_591_;
}
}
else
{
return v_r_592_;
}
}
}
else
{
lean_object* v_impl_1075_; lean_object* v___x_1076_; 
v_impl_1075_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_587_, v_l_591_);
v___x_1076_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1075_) == 0)
{
if (lean_obj_tag(v_r_592_) == 0)
{
lean_object* v_size_1077_; lean_object* v_size_1078_; lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v_l_1081_; lean_object* v_r_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_size_1077_ = lean_ctor_get(v_impl_1075_, 0);
lean_inc(v_size_1077_);
v_size_1078_ = lean_ctor_get(v_r_592_, 0);
v_k_1079_ = lean_ctor_get(v_r_592_, 1);
v_v_1080_ = lean_ctor_get(v_r_592_, 2);
v_l_1081_ = lean_ctor_get(v_r_592_, 3);
lean_inc(v_l_1081_);
v_r_1082_ = lean_ctor_get(v_r_592_, 4);
v___x_1083_ = lean_unsigned_to_nat(3u);
v___x_1084_ = lean_nat_mul(v___x_1083_, v_size_1077_);
v___x_1085_ = lean_nat_dec_lt(v___x_1084_, v_size_1078_);
lean_dec(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_l_1081_);
v___x_1086_ = lean_nat_add(v___x_1076_, v_size_1077_);
lean_dec(v_size_1077_);
v___x_1087_ = lean_nat_add(v___x_1086_, v_size_1078_);
lean_dec(v___x_1086_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 3, v_impl_1075_);
lean_ctor_set(v___x_594_, 0, v___x_1087_);
v___x_1089_ = v___x_594_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_r_592_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1154_; 
lean_inc(v_r_1082_);
lean_inc(v_v_1080_);
lean_inc(v_k_1079_);
lean_inc(v_size_1078_);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1155_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_r_592_, 2);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_r_592_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_1159_);
v___x_1092_ = v_r_592_;
v_isShared_1093_ = v_isSharedCheck_1154_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_r_592_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1154_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_size_1094_; lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v_l_1097_; lean_object* v_r_1098_; lean_object* v_size_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_size_1094_ = lean_ctor_get(v_l_1081_, 0);
v_k_1095_ = lean_ctor_get(v_l_1081_, 1);
v_v_1096_ = lean_ctor_get(v_l_1081_, 2);
v_l_1097_ = lean_ctor_get(v_l_1081_, 3);
v_r_1098_ = lean_ctor_get(v_l_1081_, 4);
v_size_1099_ = lean_ctor_get(v_r_1082_, 0);
v___x_1100_ = lean_unsigned_to_nat(2u);
v___x_1101_ = lean_nat_mul(v___x_1100_, v_size_1099_);
v___x_1102_ = lean_nat_dec_lt(v_size_1094_, v___x_1101_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1130_; 
lean_inc(v_r_1098_);
lean_inc(v_l_1097_);
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_l_1081_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; lean_object* v_unused_1132_; lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; 
v_unused_1131_ = lean_ctor_get(v_l_1081_, 4);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_l_1081_, 3);
lean_dec(v_unused_1132_);
v_unused_1133_ = lean_ctor_get(v_l_1081_, 2);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_l_1081_, 1);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_l_1081_, 0);
lean_dec(v_unused_1135_);
v___x_1104_ = v_l_1081_;
v_isShared_1105_ = v_isSharedCheck_1130_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_l_1081_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1130_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1120_; 
v___x_1106_ = lean_nat_add(v___x_1076_, v_size_1077_);
lean_dec(v_size_1077_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_size_1078_);
lean_dec(v_size_1078_);
if (lean_obj_tag(v_l_1097_) == 0)
{
lean_object* v_size_1128_; 
v_size_1128_ = lean_ctor_get(v_l_1097_, 0);
lean_inc(v_size_1128_);
v___y_1120_ = v_size_1128_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___y_1120_ = v___x_1129_;
goto v___jp_1119_;
}
v___jp_1108_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_nat_add(v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec(v___y_1110_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 4, v_r_1082_);
lean_ctor_set(v___x_1104_, 3, v_r_1098_);
lean_ctor_set(v___x_1104_, 2, v_v_1080_);
lean_ctor_set(v___x_1104_, 1, v_k_1079_);
lean_ctor_set(v___x_1104_, 0, v___x_1112_);
v___x_1114_ = v___x_1104_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_r_1098_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v_r_1082_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___x_1114_);
lean_ctor_set(v___x_1092_, 3, v___y_1109_);
lean_ctor_set(v___x_1092_, 2, v_v_1096_);
lean_ctor_set(v___x_1092_, 1, v_k_1095_);
lean_ctor_set(v___x_1092_, 0, v___x_1107_);
v___x_1116_ = v___x_1092_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v___y_1109_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
v___jp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = lean_nat_add(v___x_1106_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec(v___x_1106_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_l_1097_);
lean_ctor_set(v___x_594_, 3, v_impl_1075_);
lean_ctor_set(v___x_594_, 0, v___x_1121_);
v___x_1123_ = v___x_594_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_l_1097_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_nat_add(v___x_1076_, v_size_1099_);
if (lean_obj_tag(v_r_1098_) == 0)
{
lean_object* v_size_1125_; 
v_size_1125_ = lean_ctor_get(v_r_1098_, 0);
lean_inc(v_size_1125_);
v___y_1109_ = v___x_1123_;
v___y_1110_ = v___x_1124_;
v___y_1111_ = v_size_1125_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v___y_1109_ = v___x_1123_;
v___y_1110_ = v___x_1124_;
v___y_1111_ = v___x_1126_;
goto v___jp_1108_;
}
}
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_del_object(v___x_594_);
v___x_1136_ = lean_nat_add(v___x_1076_, v_size_1077_);
lean_dec(v_size_1077_);
v___x_1137_ = lean_nat_add(v___x_1136_, v_size_1078_);
lean_dec(v_size_1078_);
v___x_1138_ = lean_nat_add(v___x_1136_, v_size_1094_);
lean_dec(v___x_1136_);
lean_inc_ref(v_impl_1075_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_l_1081_);
lean_ctor_set(v___x_1092_, 3, v_impl_1075_);
lean_ctor_set(v___x_1092_, 2, v_v_590_);
lean_ctor_set(v___x_1092_, 1, v_k_589_);
lean_ctor_set(v___x_1092_, 0, v___x_1138_);
v___x_1140_ = v___x_1092_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_l_1081_);
v___x_1140_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_isSharedCheck_1147_ = !lean_is_exclusive(v_impl_1075_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1148_ = lean_ctor_get(v_impl_1075_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_impl_1075_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_impl_1075_, 2);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_impl_1075_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_impl_1075_, 0);
lean_dec(v_unused_1152_);
v___x_1142_ = v_impl_1075_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_impl_1075_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_r_1082_);
lean_ctor_set(v___x_1142_, 3, v___x_1140_);
lean_ctor_set(v___x_1142_, 2, v_v_1080_);
lean_ctor_set(v___x_1142_, 1, v_k_1079_);
lean_ctor_set(v___x_1142_, 0, v___x_1137_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_r_1082_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v_size_1160_ = lean_ctor_get(v_impl_1075_, 0);
lean_inc(v_size_1160_);
v___x_1161_ = lean_nat_add(v___x_1076_, v_size_1160_);
lean_dec(v_size_1160_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 3, v_impl_1075_);
lean_ctor_set(v___x_594_, 0, v___x_1161_);
v___x_1163_ = v___x_594_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_r_592_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
if (lean_obj_tag(v_r_592_) == 0)
{
lean_object* v_l_1165_; 
v_l_1165_ = lean_ctor_get(v_r_592_, 3);
lean_inc(v_l_1165_);
if (lean_obj_tag(v_l_1165_) == 0)
{
lean_object* v_r_1166_; 
v_r_1166_ = lean_ctor_get(v_r_592_, 4);
lean_inc(v_r_1166_);
if (lean_obj_tag(v_r_1166_) == 0)
{
lean_object* v_size_1167_; lean_object* v_k_1168_; lean_object* v_v_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1182_; 
v_size_1167_ = lean_ctor_get(v_r_592_, 0);
v_k_1168_ = lean_ctor_get(v_r_592_, 1);
v_v_1169_ = lean_ctor_get(v_r_592_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; 
v_unused_1183_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_1184_);
v___x_1171_ = v_r_592_;
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_v_1169_);
lean_inc(v_k_1168_);
lean_inc(v_size_1167_);
lean_dec(v_r_592_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_size_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v_size_1173_ = lean_ctor_get(v_l_1165_, 0);
v___x_1174_ = lean_nat_add(v___x_1076_, v_size_1167_);
lean_dec(v_size_1167_);
v___x_1175_ = lean_nat_add(v___x_1076_, v_size_1173_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 4, v_l_1165_);
lean_ctor_set(v___x_1171_, 3, v_impl_1075_);
lean_ctor_set(v___x_1171_, 2, v_v_590_);
lean_ctor_set(v___x_1171_, 1, v_k_589_);
lean_ctor_set(v___x_1171_, 0, v___x_1175_);
v___x_1177_ = v___x_1171_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_l_1165_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_r_1166_);
lean_ctor_set(v___x_594_, 3, v___x_1177_);
lean_ctor_set(v___x_594_, 2, v_v_1169_);
lean_ctor_set(v___x_594_, 1, v_k_1168_);
lean_ctor_set(v___x_594_, 0, v___x_1174_);
v___x_1179_ = v___x_594_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_k_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_v_1169_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_r_1166_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v_k_1185_; lean_object* v_v_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1209_; 
v_k_1185_ = lean_ctor_get(v_r_592_, 1);
v_v_1186_ = lean_ctor_get(v_r_592_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1210_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_1212_);
v___x_1188_ = v_r_592_;
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_v_1186_);
lean_inc(v_k_1185_);
lean_dec(v_r_592_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_k_1190_; lean_object* v_v_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1205_; 
v_k_1190_ = lean_ctor_get(v_l_1165_, 1);
v_v_1191_ = lean_ctor_get(v_l_1165_, 2);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_l_1165_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1206_ = lean_ctor_get(v_l_1165_, 4);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_l_1165_, 3);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_l_1165_, 0);
lean_dec(v_unused_1208_);
v___x_1193_ = v_l_1165_;
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_v_1191_);
lean_inc(v_k_1190_);
lean_dec(v_l_1165_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(3u);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 4, v_r_1166_);
lean_ctor_set(v___x_1193_, 3, v_r_1166_);
lean_ctor_set(v___x_1193_, 2, v_v_590_);
lean_ctor_set(v___x_1193_, 1, v_k_589_);
lean_ctor_set(v___x_1193_, 0, v___x_1076_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_r_1166_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_r_1166_);
v___x_1197_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 3, v_r_1166_);
lean_ctor_set(v___x_1188_, 0, v___x_1076_);
v___x_1199_ = v___x_1188_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1185_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1186_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_r_1166_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_r_1166_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_1199_);
lean_ctor_set(v___x_594_, 3, v___x_1197_);
lean_ctor_set(v___x_594_, 2, v_v_1191_);
lean_ctor_set(v___x_594_, 1, v_k_1190_);
lean_ctor_set(v___x_594_, 0, v___x_1195_);
v___x_1201_ = v___x_594_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1191_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v___x_1199_);
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
}
}
}
else
{
lean_object* v_r_1213_; 
v_r_1213_ = lean_ctor_get(v_r_592_, 4);
lean_inc(v_r_1213_);
if (lean_obj_tag(v_r_1213_) == 0)
{
lean_object* v_k_1214_; lean_object* v_v_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1226_; 
v_k_1214_ = lean_ctor_get(v_r_592_, 1);
v_v_1215_ = lean_ctor_get(v_r_592_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1227_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_1229_);
v___x_1217_ = v_r_592_;
v_isShared_1218_ = v_isSharedCheck_1226_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_dec(v_r_592_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1226_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(3u);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 4, v_l_1165_);
lean_ctor_set(v___x_1217_, 2, v_v_590_);
lean_ctor_set(v___x_1217_, 1, v_k_589_);
lean_ctor_set(v___x_1217_, 0, v___x_1076_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_l_1165_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_l_1165_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_r_1213_);
lean_ctor_set(v___x_594_, 3, v___x_1221_);
lean_ctor_set(v___x_594_, 2, v_v_1215_);
lean_ctor_set(v___x_594_, 1, v_k_1214_);
lean_ctor_set(v___x_594_, 0, v___x_1219_);
v___x_1223_ = v___x_594_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_r_1213_);
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
else
{
lean_object* v_size_1230_; lean_object* v_k_1231_; lean_object* v_v_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
v_size_1230_ = lean_ctor_get(v_r_592_, 0);
v_k_1231_ = lean_ctor_get(v_r_592_, 1);
v_v_1232_ = lean_ctor_get(v_r_592_, 2);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; 
v_unused_1244_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_1245_);
v___x_1234_ = v_r_592_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_v_1232_);
lean_inc(v_k_1231_);
lean_inc(v_size_1230_);
lean_dec(v_r_592_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 3, v_r_1213_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_size_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_r_1213_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_r_1213_);
v___x_1237_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(2u);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_1237_);
lean_ctor_set(v___x_594_, 3, v_r_1213_);
lean_ctor_set(v___x_594_, 0, v___x_1238_);
v___x_1240_ = v___x_594_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_r_1213_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v___x_1237_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
else
{
lean_object* v___x_1247_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 3, v_r_592_);
lean_ctor_set(v___x_594_, 0, v___x_1076_);
v___x_1247_ = v___x_594_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_r_592_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_r_592_);
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
}
}
else
{
return v_t_588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg___boxed(lean_object* v_k_1251_, lean_object* v_t_1252_){
_start:
{
uint64_t v_k_boxed_1253_; lean_object* v_res_1254_; 
v_k_boxed_1253_ = lean_unbox_uint64(v_k_1251_);
lean_dec_ref(v_k_1251_);
v_res_1254_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_boxed_1253_, v_t_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t v_h_1255_, lean_object* v_st_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_h_1255_, v_st_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object* v_h_1258_, lean_object* v_st_1259_){
_start:
{
uint64_t v_h_boxed_1260_; lean_object* v_res_1261_; 
v_h_boxed_1260_ = lean_unbox_uint64(v_h_1258_);
lean_dec_ref(v_h_1258_);
v_res_1261_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_1260_, v_st_1259_);
return v_res_1261_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1268_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
lean_ctor_set(v___x_1268_, 3, v___x_1267_);
lean_ctor_set(v___x_1268_, 4, v___x_1267_);
lean_ctor_set(v___x_1268_, 5, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; lean_object* v_env_1274_; lean_object* v_nextMacroScope_1275_; lean_object* v_ngen_1276_; lean_object* v_auxDeclNGen_1277_; lean_object* v_traceState_1278_; lean_object* v_messages_1279_; lean_object* v_infoState_1280_; lean_object* v_snapshotTasks_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1311_; 
v___x_1273_ = lean_st_ref_take(v___y_1271_);
v_env_1274_ = lean_ctor_get(v___x_1273_, 0);
v_nextMacroScope_1275_ = lean_ctor_get(v___x_1273_, 1);
v_ngen_1276_ = lean_ctor_get(v___x_1273_, 2);
v_auxDeclNGen_1277_ = lean_ctor_get(v___x_1273_, 3);
v_traceState_1278_ = lean_ctor_get(v___x_1273_, 4);
v_messages_1279_ = lean_ctor_get(v___x_1273_, 6);
v_infoState_1280_ = lean_ctor_get(v___x_1273_, 7);
v_snapshotTasks_1281_ = lean_ctor_get(v___x_1273_, 8);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1273_, 5);
lean_dec(v_unused_1312_);
v___x_1283_ = v___x_1273_;
v_isShared_1284_ = v_isSharedCheck_1311_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snapshotTasks_1281_);
lean_inc(v_infoState_1280_);
lean_inc(v_messages_1279_);
lean_inc(v_traceState_1278_);
lean_inc(v_auxDeclNGen_1277_);
lean_inc(v_ngen_1276_);
lean_inc(v_nextMacroScope_1275_);
lean_inc(v_env_1274_);
lean_dec(v___x_1273_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1311_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1285_ = lean_box_uint64(v_h_1269_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1286_, 0, v___x_1285_);
v___x_1287_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1288_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1287_, v_env_1274_, v___f_1286_);
v___x_1289_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 5, v___x_1289_);
lean_ctor_set(v___x_1283_, 0, v___x_1288_);
v___x_1291_ = v___x_1283_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_nextMacroScope_1275_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_ngen_1276_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_auxDeclNGen_1277_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_traceState_1278_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1310_, 6, v_messages_1279_);
lean_ctor_set(v_reuseFailAlloc_1310_, 7, v_infoState_1280_);
lean_ctor_set(v_reuseFailAlloc_1310_, 8, v_snapshotTasks_1281_);
v___x_1291_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_mctx_1294_; lean_object* v_zetaDeltaFVarIds_1295_; lean_object* v_postponed_1296_; lean_object* v_diag_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1308_; 
v___x_1292_ = lean_st_ref_set(v___y_1271_, v___x_1291_);
v___x_1293_ = lean_st_ref_take(v___y_1270_);
v_mctx_1294_ = lean_ctor_get(v___x_1293_, 0);
v_zetaDeltaFVarIds_1295_ = lean_ctor_get(v___x_1293_, 2);
v_postponed_1296_ = lean_ctor_get(v___x_1293_, 3);
v_diag_1297_ = lean_ctor_get(v___x_1293_, 4);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1293_, 1);
lean_dec(v_unused_1309_);
v___x_1299_ = v___x_1293_;
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_diag_1297_);
lean_inc(v_postponed_1296_);
lean_inc(v_zetaDeltaFVarIds_1295_);
lean_inc(v_mctx_1294_);
lean_dec(v___x_1293_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_mctx_1294_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_zetaDeltaFVarIds_1295_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_postponed_1296_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_diag_1297_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_st_ref_set(v___y_1270_, v___x_1303_);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint64_t v_h_boxed_1317_; lean_object* v_res_1318_; 
v_h_boxed_1317_ = lean_unbox_uint64(v_h_1313_);
lean_dec_ref(v_h_1313_);
v_res_1318_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1317_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(lean_object* v_t_1319_, uint64_t v_k_1320_, lean_object* v_fallback_1321_){
_start:
{
if (lean_obj_tag(v_t_1319_) == 0)
{
lean_object* v_k_1322_; lean_object* v_v_1323_; lean_object* v_l_1324_; lean_object* v_r_1325_; uint64_t v___x_1326_; uint8_t v___x_1327_; 
v_k_1322_ = lean_ctor_get(v_t_1319_, 1);
v_v_1323_ = lean_ctor_get(v_t_1319_, 2);
v_l_1324_ = lean_ctor_get(v_t_1319_, 3);
v_r_1325_ = lean_ctor_get(v_t_1319_, 4);
v___x_1326_ = lean_unbox_uint64(v_k_1322_);
v___x_1327_ = lean_uint64_dec_lt(v_k_1320_, v___x_1326_);
if (v___x_1327_ == 0)
{
uint64_t v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_unbox_uint64(v_k_1322_);
v___x_1329_ = lean_uint64_dec_eq(v_k_1320_, v___x_1328_);
if (v___x_1329_ == 0)
{
v_t_1319_ = v_r_1325_;
goto _start;
}
else
{
lean_inc(v_v_1323_);
return v_v_1323_;
}
}
else
{
v_t_1319_ = v_l_1324_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1321_);
return v_fallback_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_t_1332_, lean_object* v_k_1333_, lean_object* v_fallback_1334_){
_start:
{
uint64_t v_k_boxed_1335_; lean_object* v_res_1336_; 
v_k_boxed_1335_ = lean_unbox_uint64(v_k_1333_);
lean_dec_ref(v_k_1333_);
v_res_1336_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_t_1332_, v_k_boxed_1335_, v_fallback_1334_);
lean_dec(v_fallback_1334_);
lean_dec(v_t_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(uint64_t v_k_1337_, lean_object* v_v_1338_, lean_object* v_t_1339_){
_start:
{
if (lean_obj_tag(v_t_1339_) == 0)
{
lean_object* v_size_1340_; lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v_l_1343_; lean_object* v_r_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1628_; 
v_size_1340_ = lean_ctor_get(v_t_1339_, 0);
v_k_1341_ = lean_ctor_get(v_t_1339_, 1);
v_v_1342_ = lean_ctor_get(v_t_1339_, 2);
v_l_1343_ = lean_ctor_get(v_t_1339_, 3);
v_r_1344_ = lean_ctor_get(v_t_1339_, 4);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_t_1339_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1346_ = v_t_1339_;
v_isShared_1347_ = v_isSharedCheck_1628_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_r_1344_);
lean_inc(v_l_1343_);
lean_inc(v_v_1342_);
lean_inc(v_k_1341_);
lean_inc(v_size_1340_);
lean_dec(v_t_1339_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1628_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint64_t v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_unbox_uint64(v_k_1341_);
v___x_1349_ = lean_uint64_dec_lt(v_k_1337_, v___x_1348_);
if (v___x_1349_ == 0)
{
uint64_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = lean_unbox_uint64(v_k_1341_);
v___x_1351_ = lean_uint64_dec_eq(v_k_1337_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v_impl_1352_; lean_object* v___x_1353_; 
lean_dec(v_size_1340_);
v_impl_1352_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(v_k_1337_, v_v_1338_, v_r_1344_);
v___x_1353_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1343_) == 0)
{
lean_object* v_size_1354_; lean_object* v_size_1355_; lean_object* v_k_1356_; lean_object* v_v_1357_; lean_object* v_l_1358_; lean_object* v_r_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_size_1354_ = lean_ctor_get(v_l_1343_, 0);
v_size_1355_ = lean_ctor_get(v_impl_1352_, 0);
lean_inc(v_size_1355_);
v_k_1356_ = lean_ctor_get(v_impl_1352_, 1);
lean_inc(v_k_1356_);
v_v_1357_ = lean_ctor_get(v_impl_1352_, 2);
lean_inc(v_v_1357_);
v_l_1358_ = lean_ctor_get(v_impl_1352_, 3);
lean_inc(v_l_1358_);
v_r_1359_ = lean_ctor_get(v_impl_1352_, 4);
lean_inc(v_r_1359_);
v___x_1360_ = lean_unsigned_to_nat(3u);
v___x_1361_ = lean_nat_mul(v___x_1360_, v_size_1354_);
v___x_1362_ = lean_nat_dec_lt(v___x_1361_, v_size_1355_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec(v_r_1359_);
lean_dec(v_l_1358_);
lean_dec(v_v_1357_);
lean_dec(v_k_1356_);
v___x_1363_ = lean_nat_add(v___x_1353_, v_size_1354_);
v___x_1364_ = lean_nat_add(v___x_1363_, v_size_1355_);
lean_dec(v_size_1355_);
lean_dec(v___x_1363_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_impl_1352_);
lean_ctor_set(v___x_1346_, 0, v___x_1364_);
v___x_1366_ = v___x_1346_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_impl_1352_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
else
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v_impl_1352_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; 
v_unused_1432_ = lean_ctor_get(v_impl_1352_, 4);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_impl_1352_, 3);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_impl_1352_, 2);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_impl_1352_, 1);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_impl_1352_, 0);
lean_dec(v_unused_1436_);
v___x_1369_ = v_impl_1352_;
v_isShared_1370_ = v_isSharedCheck_1431_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v_impl_1352_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1431_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_size_1371_; lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v_l_1374_; lean_object* v_r_1375_; lean_object* v_size_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_size_1371_ = lean_ctor_get(v_l_1358_, 0);
v_k_1372_ = lean_ctor_get(v_l_1358_, 1);
v_v_1373_ = lean_ctor_get(v_l_1358_, 2);
v_l_1374_ = lean_ctor_get(v_l_1358_, 3);
v_r_1375_ = lean_ctor_get(v_l_1358_, 4);
v_size_1376_ = lean_ctor_get(v_r_1359_, 0);
v___x_1377_ = lean_unsigned_to_nat(2u);
v___x_1378_ = lean_nat_mul(v___x_1377_, v_size_1376_);
v___x_1379_ = lean_nat_dec_lt(v_size_1371_, v___x_1378_);
lean_dec(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1407_; 
lean_inc(v_r_1375_);
lean_inc(v_l_1374_);
lean_inc(v_v_1373_);
lean_inc(v_k_1372_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_l_1358_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; 
v_unused_1408_ = lean_ctor_get(v_l_1358_, 4);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_l_1358_, 3);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_l_1358_, 2);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_l_1358_, 1);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_l_1358_, 0);
lean_dec(v_unused_1412_);
v___x_1381_ = v_l_1358_;
v_isShared_1382_ = v_isSharedCheck_1407_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_l_1358_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1407_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1397_; 
v___x_1383_ = lean_nat_add(v___x_1353_, v_size_1354_);
v___x_1384_ = lean_nat_add(v___x_1383_, v_size_1355_);
lean_dec(v_size_1355_);
if (lean_obj_tag(v_l_1374_) == 0)
{
lean_object* v_size_1405_; 
v_size_1405_ = lean_ctor_get(v_l_1374_, 0);
lean_inc(v_size_1405_);
v___y_1397_ = v_size_1405_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___y_1397_ = v___x_1406_;
goto v___jp_1396_;
}
v___jp_1385_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = lean_nat_add(v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_r_1359_);
lean_ctor_set(v___x_1381_, 3, v_r_1375_);
lean_ctor_set(v___x_1381_, 2, v_v_1357_);
lean_ctor_set(v___x_1381_, 1, v_k_1356_);
lean_ctor_set(v___x_1381_, 0, v___x_1389_);
v___x_1391_ = v___x_1381_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1356_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1357_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_r_1375_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_r_1359_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v___x_1391_);
lean_ctor_set(v___x_1369_, 3, v___y_1386_);
lean_ctor_set(v___x_1369_, 2, v_v_1373_);
lean_ctor_set(v___x_1369_, 1, v_k_1372_);
lean_ctor_set(v___x_1369_, 0, v___x_1384_);
v___x_1393_ = v___x_1369_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___y_1386_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
v___jp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_nat_add(v___x_1383_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec(v___x_1383_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_l_1374_);
lean_ctor_set(v___x_1346_, 0, v___x_1398_);
v___x_1400_ = v___x_1346_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_l_1374_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_nat_add(v___x_1353_, v_size_1376_);
if (lean_obj_tag(v_r_1375_) == 0)
{
lean_object* v_size_1402_; 
v_size_1402_ = lean_ctor_get(v_r_1375_, 0);
lean_inc(v_size_1402_);
v___y_1386_ = v___x_1400_;
v___y_1387_ = v___x_1401_;
v___y_1388_ = v_size_1402_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___y_1386_ = v___x_1400_;
v___y_1387_ = v___x_1401_;
v___y_1388_ = v___x_1403_;
goto v___jp_1385_;
}
}
}
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_del_object(v___x_1346_);
v___x_1413_ = lean_nat_add(v___x_1353_, v_size_1354_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_size_1355_);
lean_dec(v_size_1355_);
v___x_1415_ = lean_nat_add(v___x_1413_, v_size_1371_);
lean_dec(v___x_1413_);
lean_inc_ref(v_l_1343_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_l_1358_);
lean_ctor_set(v___x_1369_, 3, v_l_1343_);
lean_ctor_set(v___x_1369_, 2, v_v_1342_);
lean_ctor_set(v___x_1369_, 1, v_k_1341_);
lean_ctor_set(v___x_1369_, 0, v___x_1415_);
v___x_1417_ = v___x_1369_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_l_1358_);
v___x_1417_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_isSharedCheck_1424_ = !lean_is_exclusive(v_l_1343_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; 
v_unused_1425_ = lean_ctor_get(v_l_1343_, 4);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_l_1343_, 3);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_l_1343_, 2);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_l_1343_, 1);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_l_1343_, 0);
lean_dec(v_unused_1429_);
v___x_1419_ = v_l_1343_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v_l_1343_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 4, v_r_1359_);
lean_ctor_set(v___x_1419_, 3, v___x_1417_);
lean_ctor_set(v___x_1419_, 2, v_v_1357_);
lean_ctor_set(v___x_1419_, 1, v_k_1356_);
lean_ctor_set(v___x_1419_, 0, v___x_1414_);
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1356_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1357_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_r_1359_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1437_; 
v_l_1437_ = lean_ctor_get(v_impl_1352_, 3);
lean_inc(v_l_1437_);
if (lean_obj_tag(v_l_1437_) == 0)
{
lean_object* v_r_1438_; lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1463_; 
v_r_1438_ = lean_ctor_get(v_impl_1352_, 4);
v_k_1439_ = lean_ctor_get(v_impl_1352_, 1);
v_v_1440_ = lean_ctor_get(v_impl_1352_, 2);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_impl_1352_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1464_ = lean_ctor_get(v_impl_1352_, 3);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_impl_1352_, 0);
lean_dec(v_unused_1465_);
v___x_1442_ = v_impl_1352_;
v_isShared_1443_ = v_isSharedCheck_1463_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_r_1438_);
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
lean_dec(v_impl_1352_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1463_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1459_; 
v_k_1444_ = lean_ctor_get(v_l_1437_, 1);
v_v_1445_ = lean_ctor_get(v_l_1437_, 2);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_l_1437_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; 
v_unused_1460_ = lean_ctor_get(v_l_1437_, 4);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_l_1437_, 3);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_l_1437_, 0);
lean_dec(v_unused_1462_);
v___x_1447_ = v_l_1437_;
v_isShared_1448_ = v_isSharedCheck_1459_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_v_1445_);
lean_inc(v_k_1444_);
lean_dec(v_l_1437_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1459_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1438_, 2);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 4, v_r_1438_);
lean_ctor_set(v___x_1447_, 3, v_r_1438_);
lean_ctor_set(v___x_1447_, 2, v_v_1342_);
lean_ctor_set(v___x_1447_, 1, v_k_1341_);
lean_ctor_set(v___x_1447_, 0, v___x_1353_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_r_1438_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_r_1438_);
v___x_1451_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
lean_inc(v_r_1438_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 3, v_r_1438_);
lean_ctor_set(v___x_1442_, 0, v___x_1353_);
v___x_1453_ = v___x_1442_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_r_1438_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_r_1438_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1453_);
lean_ctor_set(v___x_1346_, 3, v___x_1451_);
lean_ctor_set(v___x_1346_, 2, v_v_1445_);
lean_ctor_set(v___x_1346_, 1, v_k_1444_);
lean_ctor_set(v___x_1346_, 0, v___x_1449_);
v___x_1455_ = v___x_1346_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v___x_1453_);
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
else
{
lean_object* v_r_1466_; 
v_r_1466_ = lean_ctor_get(v_impl_1352_, 4);
lean_inc(v_r_1466_);
if (lean_obj_tag(v_r_1466_) == 0)
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1479_; 
v_k_1467_ = lean_ctor_get(v_impl_1352_, 1);
v_v_1468_ = lean_ctor_get(v_impl_1352_, 2);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_impl_1352_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; 
v_unused_1480_ = lean_ctor_get(v_impl_1352_, 4);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_impl_1352_, 3);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_impl_1352_, 0);
lean_dec(v_unused_1482_);
v___x_1470_ = v_impl_1352_;
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
lean_dec(v_impl_1352_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(3u);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v_l_1437_);
lean_ctor_set(v___x_1470_, 2, v_v_1342_);
lean_ctor_set(v___x_1470_, 1, v_k_1341_);
lean_ctor_set(v___x_1470_, 0, v___x_1353_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_l_1437_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_r_1466_);
lean_ctor_set(v___x_1346_, 3, v___x_1474_);
lean_ctor_set(v___x_1346_, 2, v_v_1468_);
lean_ctor_set(v___x_1346_, 1, v_k_1467_);
lean_ctor_set(v___x_1346_, 0, v___x_1472_);
v___x_1476_ = v___x_1346_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1467_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1468_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1466_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_unsigned_to_nat(2u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_impl_1352_);
lean_ctor_set(v___x_1346_, 3, v_r_1466_);
lean_ctor_set(v___x_1346_, 0, v___x_1483_);
v___x_1485_ = v___x_1346_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_impl_1352_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_dec(v_v_1342_);
lean_dec(v_k_1341_);
v___x_1487_ = lean_box_uint64(v_k_1337_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 2, v_v_1338_);
lean_ctor_set(v___x_1346_, 1, v___x_1487_);
v___x_1489_ = v___x_1346_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_size_1340_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_r_1344_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_object* v_impl_1491_; lean_object* v___x_1492_; 
lean_dec(v_size_1340_);
v_impl_1491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(v_k_1337_, v_v_1338_, v_l_1343_);
v___x_1492_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1344_) == 0)
{
lean_object* v_size_1493_; lean_object* v_size_1494_; lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v_l_1497_; lean_object* v_r_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_size_1493_ = lean_ctor_get(v_r_1344_, 0);
v_size_1494_ = lean_ctor_get(v_impl_1491_, 0);
lean_inc(v_size_1494_);
v_k_1495_ = lean_ctor_get(v_impl_1491_, 1);
lean_inc(v_k_1495_);
v_v_1496_ = lean_ctor_get(v_impl_1491_, 2);
lean_inc(v_v_1496_);
v_l_1497_ = lean_ctor_get(v_impl_1491_, 3);
lean_inc(v_l_1497_);
v_r_1498_ = lean_ctor_get(v_impl_1491_, 4);
lean_inc(v_r_1498_);
v___x_1499_ = lean_unsigned_to_nat(3u);
v___x_1500_ = lean_nat_mul(v___x_1499_, v_size_1493_);
v___x_1501_ = lean_nat_dec_lt(v___x_1500_, v_size_1494_);
lean_dec(v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v_r_1498_);
lean_dec(v_l_1497_);
lean_dec(v_v_1496_);
lean_dec(v_k_1495_);
v___x_1502_ = lean_nat_add(v___x_1492_, v_size_1494_);
lean_dec(v_size_1494_);
v___x_1503_ = lean_nat_add(v___x_1502_, v_size_1493_);
lean_dec(v___x_1502_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 3, v_impl_1491_);
lean_ctor_set(v___x_1346_, 0, v___x_1503_);
v___x_1505_ = v___x_1346_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_impl_1491_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_r_1344_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
else
{
lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1572_; 
v_isSharedCheck_1572_ = !lean_is_exclusive(v_impl_1491_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1573_ = lean_ctor_get(v_impl_1491_, 4);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_impl_1491_, 3);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_impl_1491_, 2);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_impl_1491_, 1);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_impl_1491_, 0);
lean_dec(v_unused_1577_);
v___x_1508_ = v_impl_1491_;
v_isShared_1509_ = v_isSharedCheck_1572_;
goto v_resetjp_1507_;
}
else
{
lean_dec(v_impl_1491_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1572_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_size_1510_; lean_object* v_size_1511_; lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v_l_1514_; lean_object* v_r_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_size_1510_ = lean_ctor_get(v_l_1497_, 0);
v_size_1511_ = lean_ctor_get(v_r_1498_, 0);
v_k_1512_ = lean_ctor_get(v_r_1498_, 1);
v_v_1513_ = lean_ctor_get(v_r_1498_, 2);
v_l_1514_ = lean_ctor_get(v_r_1498_, 3);
v_r_1515_ = lean_ctor_get(v_r_1498_, 4);
v___x_1516_ = lean_unsigned_to_nat(2u);
v___x_1517_ = lean_nat_mul(v___x_1516_, v_size_1510_);
v___x_1518_ = lean_nat_dec_lt(v_size_1511_, v___x_1517_);
lean_dec(v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1547_; 
lean_inc(v_r_1515_);
lean_inc(v_l_1514_);
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_r_1498_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1548_ = lean_ctor_get(v_r_1498_, 4);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1498_, 3);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_r_1498_, 2);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_r_1498_, 1);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_r_1498_, 0);
lean_dec(v_unused_1552_);
v___x_1520_ = v_r_1498_;
v_isShared_1521_ = v_isSharedCheck_1547_;
goto v_resetjp_1519_;
}
else
{
lean_dec(v_r_1498_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1547_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___x_1535_; lean_object* v___y_1537_; 
v___x_1522_ = lean_nat_add(v___x_1492_, v_size_1494_);
lean_dec(v_size_1494_);
v___x_1523_ = lean_nat_add(v___x_1522_, v_size_1493_);
lean_dec(v___x_1522_);
v___x_1535_ = lean_nat_add(v___x_1492_, v_size_1510_);
if (lean_obj_tag(v_l_1514_) == 0)
{
lean_object* v_size_1545_; 
v_size_1545_ = lean_ctor_get(v_l_1514_, 0);
lean_inc(v_size_1545_);
v___y_1537_ = v_size_1545_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___y_1537_ = v___x_1546_;
goto v___jp_1536_;
}
v___jp_1524_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_nat_add(v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec(v___y_1526_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 4, v_r_1344_);
lean_ctor_set(v___x_1520_, 3, v_r_1515_);
lean_ctor_set(v___x_1520_, 2, v_v_1342_);
lean_ctor_set(v___x_1520_, 1, v_k_1341_);
lean_ctor_set(v___x_1520_, 0, v___x_1528_);
v___x_1530_ = v___x_1520_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_r_1515_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_r_1344_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v___x_1530_);
lean_ctor_set(v___x_1508_, 3, v___y_1525_);
lean_ctor_set(v___x_1508_, 2, v_v_1513_);
lean_ctor_set(v___x_1508_, 1, v_k_1512_);
lean_ctor_set(v___x_1508_, 0, v___x_1523_);
v___x_1532_ = v___x_1508_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v___y_1525_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_nat_add(v___x_1535_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec(v___x_1535_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_l_1514_);
lean_ctor_set(v___x_1346_, 3, v_l_1497_);
lean_ctor_set(v___x_1346_, 2, v_v_1496_);
lean_ctor_set(v___x_1346_, 1, v_k_1495_);
lean_ctor_set(v___x_1346_, 0, v___x_1538_);
v___x_1540_ = v___x_1346_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1495_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1496_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_l_1497_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_l_1514_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_nat_add(v___x_1492_, v_size_1493_);
if (lean_obj_tag(v_r_1515_) == 0)
{
lean_object* v_size_1542_; 
v_size_1542_ = lean_ctor_get(v_r_1515_, 0);
lean_inc(v_size_1542_);
v___y_1525_ = v___x_1540_;
v___y_1526_ = v___x_1541_;
v___y_1527_ = v_size_1542_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___y_1525_ = v___x_1540_;
v___y_1526_ = v___x_1541_;
v___y_1527_ = v___x_1543_;
goto v___jp_1524_;
}
}
}
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_del_object(v___x_1346_);
v___x_1553_ = lean_nat_add(v___x_1492_, v_size_1494_);
lean_dec(v_size_1494_);
v___x_1554_ = lean_nat_add(v___x_1553_, v_size_1493_);
lean_dec(v___x_1553_);
v___x_1555_ = lean_nat_add(v___x_1492_, v_size_1493_);
v___x_1556_ = lean_nat_add(v___x_1555_, v_size_1511_);
lean_dec(v___x_1555_);
lean_inc_ref(v_r_1344_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_r_1344_);
lean_ctor_set(v___x_1508_, 3, v_r_1498_);
lean_ctor_set(v___x_1508_, 2, v_v_1342_);
lean_ctor_set(v___x_1508_, 1, v_k_1341_);
lean_ctor_set(v___x_1508_, 0, v___x_1556_);
v___x_1558_ = v___x_1508_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_r_1498_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_r_1344_);
v___x_1558_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v_r_1344_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1566_ = lean_ctor_get(v_r_1344_, 4);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v_r_1344_, 3);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_r_1344_, 2);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_r_1344_, 1);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_r_1344_, 0);
lean_dec(v_unused_1570_);
v___x_1560_ = v_r_1344_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v_r_1344_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 4, v___x_1558_);
lean_ctor_set(v___x_1560_, 3, v_l_1497_);
lean_ctor_set(v___x_1560_, 2, v_v_1496_);
lean_ctor_set(v___x_1560_, 1, v_k_1495_);
lean_ctor_set(v___x_1560_, 0, v___x_1554_);
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1495_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1496_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_l_1497_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v___x_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1578_; 
v_l_1578_ = lean_ctor_get(v_impl_1491_, 3);
lean_inc(v_l_1578_);
if (lean_obj_tag(v_l_1578_) == 0)
{
lean_object* v_r_1579_; lean_object* v_k_1580_; lean_object* v_v_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1592_; 
v_r_1579_ = lean_ctor_get(v_impl_1491_, 4);
v_k_1580_ = lean_ctor_get(v_impl_1491_, 1);
v_v_1581_ = lean_ctor_get(v_impl_1491_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_impl_1491_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; 
v_unused_1593_ = lean_ctor_get(v_impl_1491_, 3);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_impl_1491_, 0);
lean_dec(v_unused_1594_);
v___x_1583_ = v_impl_1491_;
v_isShared_1584_ = v_isSharedCheck_1592_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_r_1579_);
lean_inc(v_v_1581_);
lean_inc(v_k_1580_);
lean_dec(v_impl_1491_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1592_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1579_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 3, v_r_1579_);
lean_ctor_set(v___x_1583_, 2, v_v_1342_);
lean_ctor_set(v___x_1583_, 1, v_k_1341_);
lean_ctor_set(v___x_1583_, 0, v___x_1492_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_r_1579_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_r_1579_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1587_);
lean_ctor_set(v___x_1346_, 3, v_l_1578_);
lean_ctor_set(v___x_1346_, 2, v_v_1581_);
lean_ctor_set(v___x_1346_, 1, v_k_1580_);
lean_ctor_set(v___x_1346_, 0, v___x_1585_);
v___x_1589_ = v___x_1346_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_l_1578_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_r_1595_; 
v_r_1595_ = lean_ctor_get(v_impl_1491_, 4);
lean_inc(v_r_1595_);
if (lean_obj_tag(v_r_1595_) == 0)
{
lean_object* v_k_1596_; lean_object* v_v_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1620_; 
v_k_1596_ = lean_ctor_get(v_impl_1491_, 1);
v_v_1597_ = lean_ctor_get(v_impl_1491_, 2);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_impl_1491_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; 
v_unused_1621_ = lean_ctor_get(v_impl_1491_, 4);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_impl_1491_, 3);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_impl_1491_, 0);
lean_dec(v_unused_1623_);
v___x_1599_ = v_impl_1491_;
v_isShared_1600_ = v_isSharedCheck_1620_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_v_1597_);
lean_inc(v_k_1596_);
lean_dec(v_impl_1491_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1620_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_k_1601_; lean_object* v_v_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1616_; 
v_k_1601_ = lean_ctor_get(v_r_1595_, 1);
v_v_1602_ = lean_ctor_get(v_r_1595_, 2);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_r_1595_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; 
v_unused_1617_ = lean_ctor_get(v_r_1595_, 4);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_r_1595_, 3);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_r_1595_, 0);
lean_dec(v_unused_1619_);
v___x_1604_ = v_r_1595_;
v_isShared_1605_ = v_isSharedCheck_1616_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_v_1602_);
lean_inc(v_k_1601_);
lean_dec(v_r_1595_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1616_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_unsigned_to_nat(3u);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 4, v_l_1578_);
lean_ctor_set(v___x_1604_, 3, v_l_1578_);
lean_ctor_set(v___x_1604_, 2, v_v_1597_);
lean_ctor_set(v___x_1604_, 1, v_k_1596_);
lean_ctor_set(v___x_1604_, 0, v___x_1492_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1596_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1597_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_l_1578_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_l_1578_);
v___x_1608_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_l_1578_);
lean_ctor_set(v___x_1599_, 2, v_v_1342_);
lean_ctor_set(v___x_1599_, 1, v_k_1341_);
lean_ctor_set(v___x_1599_, 0, v___x_1492_);
v___x_1610_ = v___x_1599_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_l_1578_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_l_1578_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1610_);
lean_ctor_set(v___x_1346_, 3, v___x_1608_);
lean_ctor_set(v___x_1346_, 2, v_v_1602_);
lean_ctor_set(v___x_1346_, 1, v_k_1601_);
lean_ctor_set(v___x_1346_, 0, v___x_1606_);
v___x_1612_ = v___x_1346_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1601_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1602_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_unsigned_to_nat(2u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_r_1595_);
lean_ctor_set(v___x_1346_, 3, v_impl_1491_);
lean_ctor_set(v___x_1346_, 0, v___x_1624_);
v___x_1626_ = v___x_1346_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_impl_1491_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_r_1595_);
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
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = lean_unsigned_to_nat(1u);
v___x_1630_ = lean_box_uint64(v_k_1337_);
v___x_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
lean_ctor_set(v___x_1631_, 2, v_v_1338_);
lean_ctor_set(v___x_1631_, 3, v_t_1339_);
lean_ctor_set(v___x_1631_, 4, v_t_1339_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg___boxed(lean_object* v_k_1632_, lean_object* v_v_1633_, lean_object* v_t_1634_){
_start:
{
uint64_t v_k_boxed_1635_; lean_object* v_res_1636_; 
v_k_boxed_1635_ = lean_unbox_uint64(v_k_1632_);
lean_dec_ref(v_k_1632_);
v_res_1636_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(v_k_boxed_1635_, v_v_1633_, v_t_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1637_, lean_object* v_s_1638_){
_start:
{
uint64_t v_javascriptHash_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_javascriptHash_1639_ = lean_ctor_get_uint64(v_wi_1637_, sizeof(void*)*2);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_wi_1637_);
v___x_1641_ = lean_box(0);
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_s_1638_, v_javascriptHash_1639_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1640_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(v_javascriptHash_1639_, v___x_1643_, v_s_1638_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v_env_1650_; lean_object* v_nextMacroScope_1651_; lean_object* v_ngen_1652_; lean_object* v_auxDeclNGen_1653_; lean_object* v_traceState_1654_; lean_object* v_messages_1655_; lean_object* v_infoState_1656_; lean_object* v_snapshotTasks_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1686_; 
v___x_1649_ = lean_st_ref_take(v___y_1647_);
v_env_1650_ = lean_ctor_get(v___x_1649_, 0);
v_nextMacroScope_1651_ = lean_ctor_get(v___x_1649_, 1);
v_ngen_1652_ = lean_ctor_get(v___x_1649_, 2);
v_auxDeclNGen_1653_ = lean_ctor_get(v___x_1649_, 3);
v_traceState_1654_ = lean_ctor_get(v___x_1649_, 4);
v_messages_1655_ = lean_ctor_get(v___x_1649_, 6);
v_infoState_1656_ = lean_ctor_get(v___x_1649_, 7);
v_snapshotTasks_1657_ = lean_ctor_get(v___x_1649_, 8);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v___x_1649_, 5);
lean_dec(v_unused_1687_);
v___x_1659_ = v___x_1649_;
v_isShared_1660_ = v_isSharedCheck_1686_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_snapshotTasks_1657_);
lean_inc(v_infoState_1656_);
lean_inc(v_messages_1655_);
lean_inc(v_traceState_1654_);
lean_inc(v_auxDeclNGen_1653_);
lean_inc(v_ngen_1652_);
lean_inc(v_nextMacroScope_1651_);
lean_inc(v_env_1650_);
lean_dec(v___x_1649_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1686_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1661_, 0, v_wi_1645_);
v___x_1662_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1663_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1662_, v_env_1650_, v___f_1661_);
v___x_1664_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 5, v___x_1664_);
lean_ctor_set(v___x_1659_, 0, v___x_1663_);
v___x_1666_ = v___x_1659_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_nextMacroScope_1651_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_ngen_1652_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_auxDeclNGen_1653_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_traceState_1654_);
lean_ctor_set(v_reuseFailAlloc_1685_, 5, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1685_, 6, v_messages_1655_);
lean_ctor_set(v_reuseFailAlloc_1685_, 7, v_infoState_1656_);
lean_ctor_set(v_reuseFailAlloc_1685_, 8, v_snapshotTasks_1657_);
v___x_1666_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_mctx_1669_; lean_object* v_zetaDeltaFVarIds_1670_; lean_object* v_postponed_1671_; lean_object* v_diag_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1683_; 
v___x_1667_ = lean_st_ref_set(v___y_1647_, v___x_1666_);
v___x_1668_ = lean_st_ref_take(v___y_1646_);
v_mctx_1669_ = lean_ctor_get(v___x_1668_, 0);
v_zetaDeltaFVarIds_1670_ = lean_ctor_get(v___x_1668_, 2);
v_postponed_1671_ = lean_ctor_get(v___x_1668_, 3);
v_diag_1672_ = lean_ctor_get(v___x_1668_, 4);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; 
v_unused_1684_ = lean_ctor_get(v___x_1668_, 1);
lean_dec(v_unused_1684_);
v___x_1674_ = v___x_1668_;
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_diag_1672_);
lean_inc(v_postponed_1671_);
lean_inc(v_zetaDeltaFVarIds_1670_);
lean_inc(v_mctx_1669_);
lean_dec(v___x_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_mctx_1669_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_zetaDeltaFVarIds_1670_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_postponed_1671_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v_diag_1672_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_st_ref_set(v___y_1646_, v___x_1678_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(lean_object* v_ext_1693_, lean_object* v_b_1694_, uint8_t v_kind_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_currNamespace_1700_; lean_object* v___x_1701_; lean_object* v_env_1702_; lean_object* v_nextMacroScope_1703_; lean_object* v_ngen_1704_; lean_object* v_auxDeclNGen_1705_; lean_object* v_traceState_1706_; lean_object* v_messages_1707_; lean_object* v_infoState_1708_; lean_object* v_snapshotTasks_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1736_; 
v_currNamespace_1700_ = lean_ctor_get(v___y_1697_, 6);
lean_inc(v_currNamespace_1700_);
lean_dec_ref(v___y_1697_);
v___x_1701_ = lean_st_ref_take(v___y_1698_);
v_env_1702_ = lean_ctor_get(v___x_1701_, 0);
v_nextMacroScope_1703_ = lean_ctor_get(v___x_1701_, 1);
v_ngen_1704_ = lean_ctor_get(v___x_1701_, 2);
v_auxDeclNGen_1705_ = lean_ctor_get(v___x_1701_, 3);
v_traceState_1706_ = lean_ctor_get(v___x_1701_, 4);
v_messages_1707_ = lean_ctor_get(v___x_1701_, 6);
v_infoState_1708_ = lean_ctor_get(v___x_1701_, 7);
v_snapshotTasks_1709_ = lean_ctor_get(v___x_1701_, 8);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1701_, 5);
lean_dec(v_unused_1737_);
v___x_1711_ = v___x_1701_;
v_isShared_1712_ = v_isSharedCheck_1736_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_snapshotTasks_1709_);
lean_inc(v_infoState_1708_);
lean_inc(v_messages_1707_);
lean_inc(v_traceState_1706_);
lean_inc(v_auxDeclNGen_1705_);
lean_inc(v_ngen_1704_);
lean_inc(v_nextMacroScope_1703_);
lean_inc(v_env_1702_);
lean_dec(v___x_1701_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1736_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1713_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1702_, v_ext_1693_, v_b_1694_, v_kind_1695_, v_currNamespace_1700_);
v___x_1714_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 5, v___x_1714_);
lean_ctor_set(v___x_1711_, 0, v___x_1713_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_nextMacroScope_1703_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_ngen_1704_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_auxDeclNGen_1705_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_traceState_1706_);
lean_ctor_set(v_reuseFailAlloc_1735_, 5, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1735_, 6, v_messages_1707_);
lean_ctor_set(v_reuseFailAlloc_1735_, 7, v_infoState_1708_);
lean_ctor_set(v_reuseFailAlloc_1735_, 8, v_snapshotTasks_1709_);
v___x_1716_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_mctx_1719_; lean_object* v_zetaDeltaFVarIds_1720_; lean_object* v_postponed_1721_; lean_object* v_diag_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
v___x_1717_ = lean_st_ref_set(v___y_1698_, v___x_1716_);
v___x_1718_ = lean_st_ref_take(v___y_1696_);
v_mctx_1719_ = lean_ctor_get(v___x_1718_, 0);
v_zetaDeltaFVarIds_1720_ = lean_ctor_get(v___x_1718_, 2);
v_postponed_1721_ = lean_ctor_get(v___x_1718_, 3);
v_diag_1722_ = lean_ctor_get(v___x_1718_, 4);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1718_, 1);
lean_dec(v_unused_1734_);
v___x_1724_ = v___x_1718_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_diag_1722_);
lean_inc(v_postponed_1721_);
lean_inc(v_zetaDeltaFVarIds_1720_);
lean_inc(v_mctx_1719_);
lean_dec(v___x_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_mctx_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_zetaDeltaFVarIds_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_postponed_1721_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_diag_1722_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_st_ref_set(v___y_1696_, v___x_1728_);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg___boxed(lean_object* v_ext_1738_, lean_object* v_b_1739_, lean_object* v_kind_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_kind_boxed_1745_; lean_object* v_res_1746_; 
v_kind_boxed_1745_ = lean_unbox(v_kind_1740_);
v_res_1746_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v_ext_1738_, v_b_1739_, v_kind_boxed_1745_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec(v___y_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1747_, lean_object* v_n_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1756_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1757_ = lean_box_uint64(v_h_1747_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_n_1748_);
v___x_1759_ = 2;
v___x_1760_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v___x_1756_, v___x_1758_, v___x_1759_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1761_, lean_object* v_n_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint64_t v_h_boxed_1770_; lean_object* v_res_1771_; 
v_h_boxed_1770_ = lean_unbox_uint64(v_h_1761_);
lean_dec_ref(v_h_1761_);
v_res_1771_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1770_, v_n_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1772_, lean_object* v_n_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1782_ = lean_box_uint64(v_h_1772_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_n_1773_);
v___x_1784_ = 0;
v___x_1785_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v___x_1781_, v___x_1783_, v___x_1784_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1786_, lean_object* v_n_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint64_t v_h_boxed_1795_; lean_object* v_res_1796_; 
v_h_boxed_1795_ = lean_unbox_uint64(v_h_1786_);
lean_dec_ref(v_h_1786_);
v_res_1796_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1795_, v_n_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1797_, lean_object* v_declName_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___x_1801_; lean_object* v_env_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1801_ = 0;
v_env_1802_ = l_Lean_Environment_setExporting(v_env_1797_, v___x_1801_);
lean_inc(v_declName_1798_);
v___x_1803_ = l_Lean_mkPrivateName(v_env_1802_, v_declName_1798_);
v___x_1804_ = 1;
lean_inc_ref(v_env_1802_);
v___x_1805_ = l_Lean_Environment_contains(v_env_1802_, v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = l_Lean_privateToUserName(v_declName_1798_);
v___x_1807_ = l_Lean_Environment_contains(v_env_1802_, v___x_1806_, v___x_1804_);
v___x_1808_ = lean_box(v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___y_1800_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v_env_1802_);
lean_dec(v_declName_1798_);
v___x_1810_ = lean_box(v___x_1805_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v___y_1800_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1812_, lean_object* v_declName_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1812_, v_declName_1813_, v___y_1814_, v___y_1815_);
lean_dec_ref(v___y_1814_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v_env_1824_; lean_object* v___x_1825_; lean_object* v_mctx_1826_; lean_object* v_lctx_1827_; lean_object* v_options_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1823_ = lean_st_ref_get(v___y_1821_);
v_env_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_ref(v_env_1824_);
lean_dec(v___x_1823_);
v___x_1825_ = lean_st_ref_get(v___y_1819_);
v_mctx_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_mctx_1826_);
lean_dec(v___x_1825_);
v_lctx_1827_ = lean_ctor_get(v___y_1818_, 2);
v_options_1828_ = lean_ctor_get(v___y_1820_, 2);
lean_inc_ref(v_options_1828_);
lean_inc_ref(v_lctx_1827_);
v___x_1829_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1829_, 0, v_env_1824_);
lean_ctor_set(v___x_1829_, 1, v_mctx_1826_);
lean_ctor_set(v___x_1829_, 2, v_lctx_1827_);
lean_ctor_set(v___x_1829_, 3, v_options_1828_);
v___x_1830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_msgData_1817_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1839_; double v___x_1840_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_float_of_nat(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_cls_1843_, lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_ref_1850_; lean_object* v___x_1851_; lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1896_; 
v_ref_1850_ = lean_ctor_get(v___y_1847_, 5);
v___x_1851_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1896_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1896_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v_traceState_1857_; lean_object* v_env_1858_; lean_object* v_nextMacroScope_1859_; lean_object* v_ngen_1860_; lean_object* v_auxDeclNGen_1861_; lean_object* v_cache_1862_; lean_object* v_messages_1863_; lean_object* v_infoState_1864_; lean_object* v_snapshotTasks_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1895_; 
v___x_1856_ = lean_st_ref_take(v___y_1848_);
v_traceState_1857_ = lean_ctor_get(v___x_1856_, 4);
v_env_1858_ = lean_ctor_get(v___x_1856_, 0);
v_nextMacroScope_1859_ = lean_ctor_get(v___x_1856_, 1);
v_ngen_1860_ = lean_ctor_get(v___x_1856_, 2);
v_auxDeclNGen_1861_ = lean_ctor_get(v___x_1856_, 3);
v_cache_1862_ = lean_ctor_get(v___x_1856_, 5);
v_messages_1863_ = lean_ctor_get(v___x_1856_, 6);
v_infoState_1864_ = lean_ctor_get(v___x_1856_, 7);
v_snapshotTasks_1865_ = lean_ctor_get(v___x_1856_, 8);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1867_ = v___x_1856_;
v_isShared_1868_ = v_isSharedCheck_1895_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snapshotTasks_1865_);
lean_inc(v_infoState_1864_);
lean_inc(v_messages_1863_);
lean_inc(v_cache_1862_);
lean_inc(v_traceState_1857_);
lean_inc(v_auxDeclNGen_1861_);
lean_inc(v_ngen_1860_);
lean_inc(v_nextMacroScope_1859_);
lean_inc(v_env_1858_);
lean_dec(v___x_1856_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1895_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
uint64_t v_tid_1869_; lean_object* v_traces_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1894_; 
v_tid_1869_ = lean_ctor_get_uint64(v_traceState_1857_, sizeof(void*)*1);
v_traces_1870_ = lean_ctor_get(v_traceState_1857_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_traceState_1857_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1872_ = v_traceState_1857_;
v_isShared_1873_ = v_isSharedCheck_1894_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_traces_1870_);
lean_dec(v_traceState_1857_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1894_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; double v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__0);
v___x_1876_ = 0;
v___x_1877_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1878_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1878_, 0, v_cls_1843_);
lean_ctor_set(v___x_1878_, 1, v___x_1874_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
lean_ctor_set_float(v___x_1878_, sizeof(void*)*3, v___x_1875_);
lean_ctor_set_float(v___x_1878_, sizeof(void*)*3 + 8, v___x_1875_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*3 + 16, v___x_1876_);
v___x_1879_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___closed__1));
v___x_1880_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v_a_1852_);
lean_ctor_set(v___x_1880_, 2, v___x_1879_);
lean_inc(v_ref_1850_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_ref_1850_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_PersistentArray_push___redArg(v_traces_1870_, v___x_1881_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1882_);
v___x_1884_ = v___x_1872_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1882_);
lean_ctor_set_uint64(v_reuseFailAlloc_1893_, sizeof(void*)*1, v_tid_1869_);
v___x_1884_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 4, v___x_1884_);
v___x_1886_ = v___x_1867_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_env_1858_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_nextMacroScope_1859_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_ngen_1860_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_auxDeclNGen_1861_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1892_, 5, v_cache_1862_);
lean_ctor_set(v_reuseFailAlloc_1892_, 6, v_messages_1863_);
lean_ctor_set(v_reuseFailAlloc_1892_, 7, v_infoState_1864_);
lean_ctor_set(v_reuseFailAlloc_1892_, 8, v_snapshotTasks_1865_);
v___x_1886_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = lean_st_ref_set(v___y_1848_, v___x_1886_);
v___x_1888_ = lean_box(0);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1888_);
v___x_1890_ = v___x_1854_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_cls_1897_, lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_cls_1897_, v_msg_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_options_1911_; uint8_t v_hasTrace_1912_; 
v_options_1911_ = lean_ctor_get(v___y_1909_, 2);
v_hasTrace_1912_ = lean_ctor_get_uint8(v_options_1911_, sizeof(void*)*1);
if (v_hasTrace_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v_cls_1908_);
v___x_1913_ = lean_box(v_hasTrace_1912_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
else
{
lean_object* v_inheritedTraceOptions_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_inheritedTraceOptions_1915_ = lean_ctor_get(v___y_1909_, 13);
v___x_1916_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1917_ = l_Lean_Name_append(v___x_1916_, v_cls_1908_);
v___x_1918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1915_, v_options_1911_, v___x_1917_);
lean_dec(v___x_1917_);
v___x_1919_ = lean_box(v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1921_, v___y_1922_);
lean_dec_ref(v___y_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_as_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
if (lean_obj_tag(v_as_1925_) == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v_head_1935_; lean_object* v_tail_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1952_; 
v_head_1935_ = lean_ctor_get(v_as_1925_, 0);
lean_inc(v_head_1935_);
v_tail_1936_ = lean_ctor_get(v_as_1925_, 1);
lean_inc(v_tail_1936_);
lean_dec_ref(v_as_1925_);
v_fst_1937_ = lean_ctor_get(v_head_1935_, 0);
lean_inc(v_fst_1937_);
v_snd_1938_ = lean_ctor_get(v_head_1935_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_head_1935_);
lean_inc(v_fst_1937_);
v___x_1939_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_1937_, v___y_1930_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1952_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1952_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
if (v___x_1944_ == 0)
{
lean_del_object(v___x_1942_);
lean_dec(v_snd_1938_);
lean_dec(v_fst_1937_);
v_as_1925_ = v_tail_1936_;
goto _start;
}
else
{
lean_object* v___x_1947_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 3);
lean_ctor_set(v___x_1942_, 0, v_snd_1938_);
v___x_1947_ = v___x_1942_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_snd_1938_);
v___x_1947_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = l_Lean_MessageData_ofFormat(v___x_1947_);
v___x_1949_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_fst_1937_, v___x_1948_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_dec_ref(v___x_1949_);
v_as_1925_ = v_tail_1936_;
goto _start;
}
else
{
lean_dec(v_tail_1936_);
return v___x_1949_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_as_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_as_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1961_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_box(1);
v___x_1963_ = l_Lean_MessageData_ofFormat(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__2));
v___x_1968_ = l_Lean_MessageData_ofFormat(v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(lean_object* v_x_1969_, lean_object* v_x_1970_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 0)
{
return v_x_1969_;
}
else
{
lean_object* v_head_1971_; lean_object* v_tail_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1994_; 
v_head_1971_ = lean_ctor_get(v_x_1970_, 0);
v_tail_1972_ = lean_ctor_get(v_x_1970_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_x_1970_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1974_ = v_x_1970_;
v_isShared_1975_ = v_isSharedCheck_1994_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_tail_1972_);
lean_inc(v_head_1971_);
lean_dec(v_x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1994_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_before_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1992_; 
v_before_1976_ = lean_ctor_get(v_head_1971_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_head_1971_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_head_1971_, 1);
lean_dec(v_unused_1993_);
v___x_1978_ = v_head_1971_;
v_isShared_1979_ = v_isSharedCheck_1992_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_before_1976_);
lean_dec(v_head_1971_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1992_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0);
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 7);
lean_ctor_set(v___x_1978_, 1, v___x_1980_);
lean_ctor_set(v___x_1978_, 0, v_x_1969_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_x_1969_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__3);
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 7);
lean_ctor_set(v___x_1974_, 1, v___x_1983_);
lean_ctor_set(v___x_1974_, 0, v___x_1982_);
v___x_1985_ = v___x_1974_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = l_Lean_MessageData_ofSyntax(v_before_1976_);
v___x_1987_ = l_Lean_indentD(v___x_1986_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v_x_1969_ = v___x_1988_;
v_x_1970_ = v_tail_1972_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__22(lean_object* v_opts_1995_, lean_object* v_opt_1996_){
_start:
{
lean_object* v_name_1997_; lean_object* v_defValue_1998_; lean_object* v_map_1999_; lean_object* v___x_2000_; 
v_name_1997_ = lean_ctor_get(v_opt_1996_, 0);
v_defValue_1998_ = lean_ctor_get(v_opt_1996_, 1);
v_map_1999_ = lean_ctor_get(v_opts_1995_, 0);
v___x_2000_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1999_, v_name_1997_);
if (lean_obj_tag(v___x_2000_) == 0)
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_unbox(v_defValue_1998_);
return v___x_2001_;
}
else
{
lean_object* v_val_2002_; 
v_val_2002_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_val_2002_);
lean_dec_ref(v___x_2000_);
if (lean_obj_tag(v_val_2002_) == 1)
{
uint8_t v_v_2003_; 
v_v_2003_ = lean_ctor_get_uint8(v_val_2002_, 0);
lean_dec_ref(v_val_2002_);
return v_v_2003_;
}
else
{
uint8_t v___x_2004_; 
lean_dec(v_val_2002_);
v___x_2004_ = lean_unbox(v_defValue_1998_);
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__22___boxed(lean_object* v_opts_2005_, lean_object* v_opt_2006_){
_start:
{
uint8_t v_res_2007_; lean_object* v_r_2008_; 
v_res_2007_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__22(v_opts_2005_, v_opt_2006_);
lean_dec_ref(v_opt_2006_);
lean_dec_ref(v_opts_2005_);
v_r_2008_ = lean_box(v_res_2007_);
return v_r_2008_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__1));
v___x_2013_ = l_Lean_MessageData_ofFormat(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(lean_object* v_msgData_2014_, lean_object* v_macroStack_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_options_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_options_2018_ = lean_ctor_get(v___y_2016_, 2);
v___x_2019_ = l_Lean_Elab_pp_macroStack;
v___x_2020_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__22(v_options_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v_macroStack_2015_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_msgData_2014_);
return v___x_2021_;
}
else
{
if (lean_obj_tag(v_macroStack_2015_) == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_msgData_2014_);
return v___x_2022_;
}
else
{
lean_object* v_head_2023_; lean_object* v_after_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2039_; 
v_head_2023_ = lean_ctor_get(v_macroStack_2015_, 0);
lean_inc(v_head_2023_);
v_after_2024_ = lean_ctor_get(v_head_2023_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_head_2023_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v_head_2023_, 0);
lean_dec(v_unused_2040_);
v___x_2026_ = v_head_2023_;
v_isShared_2027_ = v_isSharedCheck_2039_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_after_2024_);
lean_dec(v_head_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2039_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23___closed__0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 7);
lean_ctor_set(v___x_2026_, 1, v___x_2028_);
lean_ctor_set(v___x_2026_, 0, v_msgData_2014_);
v___x_2030_ = v___x_2026_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_msgData_2014_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_msgData_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2031_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___closed__2);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_MessageData_ofSyntax(v_after_2024_);
v___x_2034_ = l_Lean_indentD(v___x_2033_);
v_msgData_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2035_, 0, v___x_2032_);
lean_ctor_set(v_msgData_2035_, 1, v___x_2034_);
v___x_2036_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18_spec__23(v_msgData_2035_, v_macroStack_2015_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg___boxed(lean_object* v_msgData_2041_, lean_object* v_macroStack_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_msgData_2041_, v_macroStack_2042_, v___y_2043_);
lean_dec_ref(v___y_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_ref_2054_; lean_object* v___x_2055_; lean_object* v_a_2056_; lean_object* v_macroStack_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
v_ref_2054_ = lean_ctor_get(v___y_2051_, 5);
v___x_2055_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msg_2046_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v_macroStack_2057_ = lean_ctor_get(v___y_2047_, 1);
lean_inc(v_macroStack_2057_);
lean_dec_ref(v___y_2047_);
lean_inc(v_macroStack_2057_);
v___x_2058_ = l_Lean_Elab_getBetterRef(v_ref_2054_, v_macroStack_2057_);
v___x_2059_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_a_2056_, v_macroStack_2057_, v___y_2051_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2058_);
lean_ctor_set(v___x_2064_, 1, v_a_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2078_, lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_fileName_2087_; lean_object* v_fileMap_2088_; lean_object* v_options_2089_; lean_object* v_currRecDepth_2090_; lean_object* v_maxRecDepth_2091_; lean_object* v_ref_2092_; lean_object* v_currNamespace_2093_; lean_object* v_openDecls_2094_; lean_object* v_initHeartbeats_2095_; lean_object* v_maxHeartbeats_2096_; lean_object* v_quotContext_2097_; lean_object* v_currMacroScope_2098_; uint8_t v_diag_2099_; lean_object* v_cancelTk_x3f_2100_; uint8_t v_suppressElabErrors_2101_; lean_object* v_inheritedTraceOptions_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2111_; 
v_fileName_2087_ = lean_ctor_get(v___y_2084_, 0);
v_fileMap_2088_ = lean_ctor_get(v___y_2084_, 1);
v_options_2089_ = lean_ctor_get(v___y_2084_, 2);
v_currRecDepth_2090_ = lean_ctor_get(v___y_2084_, 3);
v_maxRecDepth_2091_ = lean_ctor_get(v___y_2084_, 4);
v_ref_2092_ = lean_ctor_get(v___y_2084_, 5);
v_currNamespace_2093_ = lean_ctor_get(v___y_2084_, 6);
v_openDecls_2094_ = lean_ctor_get(v___y_2084_, 7);
v_initHeartbeats_2095_ = lean_ctor_get(v___y_2084_, 8);
v_maxHeartbeats_2096_ = lean_ctor_get(v___y_2084_, 9);
v_quotContext_2097_ = lean_ctor_get(v___y_2084_, 10);
v_currMacroScope_2098_ = lean_ctor_get(v___y_2084_, 11);
v_diag_2099_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*14);
v_cancelTk_x3f_2100_ = lean_ctor_get(v___y_2084_, 12);
v_suppressElabErrors_2101_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2102_ = lean_ctor_get(v___y_2084_, 13);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___y_2084_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2104_ = v___y_2084_;
v_isShared_2105_ = v_isSharedCheck_2111_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_inheritedTraceOptions_2102_);
lean_inc(v_cancelTk_x3f_2100_);
lean_inc(v_currMacroScope_2098_);
lean_inc(v_quotContext_2097_);
lean_inc(v_maxHeartbeats_2096_);
lean_inc(v_initHeartbeats_2095_);
lean_inc(v_openDecls_2094_);
lean_inc(v_currNamespace_2093_);
lean_inc(v_ref_2092_);
lean_inc(v_maxRecDepth_2091_);
lean_inc(v_currRecDepth_2090_);
lean_inc(v_options_2089_);
lean_inc(v_fileMap_2088_);
lean_inc(v_fileName_2087_);
lean_dec(v___y_2084_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2111_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_ref_2106_; lean_object* v___x_2108_; 
v_ref_2106_ = l_Lean_replaceRef(v_ref_2078_, v_ref_2092_);
lean_dec(v_ref_2092_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 5, v_ref_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fileName_2087_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_fileMap_2088_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_options_2089_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_currRecDepth_2090_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_maxRecDepth_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_ref_2106_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_currNamespace_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v_openDecls_2094_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v_initHeartbeats_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 9, v_maxHeartbeats_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 10, v_quotContext_2097_);
lean_ctor_set(v_reuseFailAlloc_2110_, 11, v_currMacroScope_2098_);
lean_ctor_set(v_reuseFailAlloc_2110_, 12, v_cancelTk_x3f_2100_);
lean_ctor_set(v_reuseFailAlloc_2110_, 13, v_inheritedTraceOptions_2102_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*14, v_diag_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*14 + 1, v_suppressElabErrors_2101_);
v___x_2108_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___x_2108_, v___y_2085_);
lean_dec_ref(v___x_2108_);
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2112_, lean_object* v_msg_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2112_, v_msg_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v_ref_2112_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_env_2122_, lean_object* v_currNamespace_2123_, lean_object* v_openDecls_2124_, lean_object* v_n_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = l_Lean_ResolveName_resolveNamespace(v_env_2122_, v_currNamespace_2123_, v_openDecls_2124_, v_n_2125_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___y_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_env_2130_, lean_object* v_currNamespace_2131_, lean_object* v_openDecls_2132_, lean_object* v_n_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_env_2130_, v_currNamespace_2131_, v_openDecls_2132_, v_n_2133_, v___y_2134_, v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = l_Lean_maxRecDepthErrorMessage;
v___x_2143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__3);
v___x_2145_ = l_Lean_MessageData_ofFormat(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__4);
v___x_2147_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__2));
v___x_2148_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v___x_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg(lean_object* v_ref_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___closed__5);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_ref_2149_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg___boxed(lean_object* v_ref_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg(v_ref_2154_);
return v_res_2156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg(lean_object* v_keys_2157_, lean_object* v_i_2158_, lean_object* v_k_2159_){
_start:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_array_get_size(v_keys_2157_);
v___x_2161_ = lean_nat_dec_lt(v_i_2158_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_dec(v_i_2158_);
return v___x_2161_;
}
else
{
lean_object* v_k_x27_2162_; uint8_t v___x_2163_; 
v_k_x27_2162_ = lean_array_fget_borrowed(v_keys_2157_, v_i_2158_);
v___x_2163_ = l_Lean_instBEqExtraModUse_beq(v_k_2159_, v_k_x27_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_nat_add(v_i_2158_, v___x_2164_);
lean_dec(v_i_2158_);
v_i_2158_ = v___x_2165_;
goto _start;
}
else
{
lean_dec(v_i_2158_);
return v___x_2163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg___boxed(lean_object* v_keys_2167_, lean_object* v_i_2168_, lean_object* v_k_2169_){
_start:
{
uint8_t v_res_2170_; lean_object* v_r_2171_; 
v_res_2170_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg(v_keys_2167_, v_i_2168_, v_k_2169_);
lean_dec_ref(v_k_2169_);
lean_dec_ref(v_keys_2167_);
v_r_2171_ = lean_box(v_res_2170_);
return v_r_2171_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__0(void){
_start:
{
size_t v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; 
v___x_2172_ = ((size_t)5ULL);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_shift_left(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__1(void){
_start:
{
size_t v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; 
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__0);
v___x_2177_ = lean_usize_sub(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg(lean_object* v_x_2178_, size_t v_x_2179_, lean_object* v_x_2180_){
_start:
{
if (lean_obj_tag(v_x_2178_) == 0)
{
lean_object* v_es_2181_; lean_object* v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; lean_object* v_j_2186_; lean_object* v___x_2187_; 
v_es_2181_ = lean_ctor_get(v_x_2178_, 0);
lean_inc_ref(v_es_2181_);
lean_dec_ref(v_x_2178_);
v___x_2182_ = lean_box(2);
v___x_2183_ = ((size_t)5ULL);
v___x_2184_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___closed__1);
v___x_2185_ = lean_usize_land(v_x_2179_, v___x_2184_);
v_j_2186_ = lean_usize_to_nat(v___x_2185_);
v___x_2187_ = lean_array_get(v___x_2182_, v_es_2181_, v_j_2186_);
lean_dec(v_j_2186_);
lean_dec_ref(v_es_2181_);
switch(lean_obj_tag(v___x_2187_))
{
case 0:
{
lean_object* v_key_2188_; uint8_t v___x_2189_; 
v_key_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_key_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = l_Lean_instBEqExtraModUse_beq(v_x_2180_, v_key_2188_);
lean_dec(v_key_2188_);
return v___x_2189_;
}
case 1:
{
lean_object* v_node_2190_; size_t v___x_2191_; 
v_node_2190_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_node_2190_);
lean_dec_ref(v___x_2187_);
v___x_2191_ = lean_usize_shift_right(v_x_2179_, v___x_2183_);
v_x_2178_ = v_node_2190_;
v_x_2179_ = v___x_2191_;
goto _start;
}
default: 
{
uint8_t v___x_2193_; 
v___x_2193_ = 0;
return v___x_2193_;
}
}
}
else
{
lean_object* v_ks_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_ks_2194_ = lean_ctor_get(v_x_2178_, 0);
lean_inc_ref(v_ks_2194_);
lean_dec_ref(v_x_2178_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg(v_ks_2194_, v___x_2195_, v_x_2180_);
lean_dec_ref(v_ks_2194_);
return v___x_2196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg___boxed(lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
size_t v_x_33583__boxed_2200_; uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_x_33583__boxed_2200_ = lean_unbox_usize(v_x_2198_);
lean_dec(v_x_2198_);
v_res_2201_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg(v_x_2197_, v_x_33583__boxed_2200_, v_x_2199_);
lean_dec_ref(v_x_2199_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg(lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
uint64_t v___x_2205_; size_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = l_Lean_instHashableExtraModUse_hash(v_x_2204_);
v___x_2206_ = lean_uint64_to_usize(v___x_2205_);
v___x_2207_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg(v_x_2203_, v___x_2206_, v_x_2204_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg___boxed(lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
uint8_t v_res_2210_; lean_object* v_r_2211_; 
v_res_2210_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg(v_x_2208_, v_x_2209_);
lean_dec_ref(v_x_2209_);
v_r_2211_ = lean_box(v_res_2210_);
return v_r_2211_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__1));
v___x_2215_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__0));
v___x_2216_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__6(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__5));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__8(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__7));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__9(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__11(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__10));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__13(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__12));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6(lean_object* v_mod_2238_, uint8_t v_isMeta_2239_, lean_object* v_hint_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_env_2249_; uint8_t v_isExporting_2250_; lean_object* v___x_2251_; lean_object* v_env_2252_; lean_object* v___x_2253_; lean_object* v_entry_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2248_ = lean_st_ref_get(v___y_2246_);
v_env_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_ref(v_env_2249_);
lean_dec(v___x_2248_);
v_isExporting_2250_ = lean_ctor_get_uint8(v_env_2249_, sizeof(void*)*8);
lean_dec_ref(v_env_2249_);
v___x_2251_ = lean_st_ref_get(v___y_2246_);
v_env_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc_ref(v_env_2252_);
lean_dec(v___x_2251_);
v___x_2253_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__2);
lean_inc(v_mod_2238_);
v_entry_2254_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2254_, 0, v_mod_2238_);
lean_ctor_set_uint8(v_entry_2254_, sizeof(void*)*1, v_isExporting_2250_);
lean_ctor_set_uint8(v_entry_2254_, sizeof(void*)*1 + 1, v_isMeta_2239_);
v___x_2255_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2256_ = lean_box(1);
v___x_2257_ = lean_box(0);
v___x_2300_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2253_, v___x_2255_, v_env_2252_, v___x_2256_, v___x_2257_);
v___x_2301_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg(v___x_2300_, v_entry_2254_);
if (v___x_2301_ == 0)
{
lean_object* v_cls_2302_; lean_object* v___x_2303_; lean_object* v_a_2304_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2311_; lean_object* v___y_2312_; uint8_t v___x_2324_; 
v_cls_2302_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__4));
v___x_2303_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2302_, v___y_2245_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
v___x_2324_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
if (v___x_2324_ == 0)
{
lean_dec(v_hint_2240_);
lean_dec(v_mod_2238_);
v___y_2259_ = v___y_2244_;
v___y_2260_ = v___y_2246_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2325_; lean_object* v___y_2327_; 
v___x_2325_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__11);
if (v_isExporting_2250_ == 0)
{
lean_object* v___x_2334_; 
v___x_2334_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__16));
v___y_2327_ = v___x_2334_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2335_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__17));
v___y_2327_ = v___x_2335_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2328_ = l_Lean_stringToMessageData(v___y_2327_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2325_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__13);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
if (v_isMeta_2239_ == 0)
{
lean_object* v___x_2332_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__14));
v___y_2311_ = v___x_2331_;
v___y_2312_ = v___x_2332_;
goto v___jp_2310_;
}
else
{
lean_object* v___x_2333_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__15));
v___y_2311_ = v___x_2331_;
v___y_2312_ = v___x_2333_;
goto v___jp_2310_;
}
}
}
v___jp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___y_2306_);
lean_ctor_set(v___x_2308_, 1, v___y_2307_);
v___x_2309_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_cls_2302_, v___x_2308_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_dec_ref(v___x_2309_);
v___y_2259_ = v___y_2244_;
v___y_2260_ = v___y_2246_;
goto v___jp_2258_;
}
else
{
lean_dec_ref(v_entry_2254_);
return v___x_2309_;
}
}
v___jp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2313_ = l_Lean_stringToMessageData(v___y_2312_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___y_2311_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__6);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_MessageData_ofName(v_mod_2238_);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_Name_isAnonymous(v_hint_2240_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__8);
v___x_2321_ = l_Lean_MessageData_ofName(v_hint_2240_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___y_2306_ = v___x_2318_;
v___y_2307_ = v___x_2322_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2323_; 
lean_dec(v_hint_2240_);
v___x_2323_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___closed__9);
v___y_2306_ = v___x_2318_;
v___y_2307_ = v___x_2323_;
goto v___jp_2305_;
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v_entry_2254_);
lean_dec(v_hint_2240_);
lean_dec(v_mod_2238_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
v___jp_2258_:
{
lean_object* v___x_2261_; lean_object* v_toEnvExtension_2262_; lean_object* v_env_2263_; lean_object* v_nextMacroScope_2264_; lean_object* v_ngen_2265_; lean_object* v_auxDeclNGen_2266_; lean_object* v_traceState_2267_; lean_object* v_messages_2268_; lean_object* v_infoState_2269_; lean_object* v_snapshotTasks_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2298_; 
v___x_2261_ = lean_st_ref_take(v___y_2260_);
v_toEnvExtension_2262_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref(v_toEnvExtension_2262_);
v_env_2263_ = lean_ctor_get(v___x_2261_, 0);
v_nextMacroScope_2264_ = lean_ctor_get(v___x_2261_, 1);
v_ngen_2265_ = lean_ctor_get(v___x_2261_, 2);
v_auxDeclNGen_2266_ = lean_ctor_get(v___x_2261_, 3);
v_traceState_2267_ = lean_ctor_get(v___x_2261_, 4);
v_messages_2268_ = lean_ctor_get(v___x_2261_, 6);
v_infoState_2269_ = lean_ctor_get(v___x_2261_, 7);
v_snapshotTasks_2270_ = lean_ctor_get(v___x_2261_, 8);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v___x_2261_, 5);
lean_dec(v_unused_2299_);
v___x_2272_ = v___x_2261_;
v_isShared_2273_ = v_isSharedCheck_2298_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_snapshotTasks_2270_);
lean_inc(v_infoState_2269_);
lean_inc(v_messages_2268_);
lean_inc(v_traceState_2267_);
lean_inc(v_auxDeclNGen_2266_);
lean_inc(v_ngen_2265_);
lean_inc(v_nextMacroScope_2264_);
lean_inc(v_env_2263_);
lean_dec(v___x_2261_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2298_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_asyncMode_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v_asyncMode_2274_ = lean_ctor_get(v_toEnvExtension_2262_, 2);
lean_inc(v_asyncMode_2274_);
lean_dec_ref(v_toEnvExtension_2262_);
v___x_2275_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2255_, v_env_2263_, v_entry_2254_, v_asyncMode_2274_, v___x_2257_);
lean_dec(v_asyncMode_2274_);
v___x_2276_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 5, v___x_2276_);
lean_ctor_set(v___x_2272_, 0, v___x_2275_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_nextMacroScope_2264_);
lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_ngen_2265_);
lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_auxDeclNGen_2266_);
lean_ctor_set(v_reuseFailAlloc_2297_, 4, v_traceState_2267_);
lean_ctor_set(v_reuseFailAlloc_2297_, 5, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2297_, 6, v_messages_2268_);
lean_ctor_set(v_reuseFailAlloc_2297_, 7, v_infoState_2269_);
lean_ctor_set(v_reuseFailAlloc_2297_, 8, v_snapshotTasks_2270_);
v___x_2278_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v_mctx_2281_; lean_object* v_zetaDeltaFVarIds_2282_; lean_object* v_postponed_2283_; lean_object* v_diag_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2295_; 
v___x_2279_ = lean_st_ref_set(v___y_2260_, v___x_2278_);
v___x_2280_ = lean_st_ref_take(v___y_2259_);
v_mctx_2281_ = lean_ctor_get(v___x_2280_, 0);
v_zetaDeltaFVarIds_2282_ = lean_ctor_get(v___x_2280_, 2);
v_postponed_2283_ = lean_ctor_get(v___x_2280_, 3);
v_diag_2284_ = lean_ctor_get(v___x_2280_, 4);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v___x_2280_, 1);
lean_dec(v_unused_2296_);
v___x_2286_ = v___x_2280_;
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_diag_2284_);
lean_inc(v_postponed_2283_);
lean_inc(v_zetaDeltaFVarIds_2282_);
lean_inc(v_mctx_2281_);
lean_dec(v___x_2280_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 1, v___x_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_mctx_2281_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_zetaDeltaFVarIds_2282_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_postponed_2283_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v_diag_2284_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_st_ref_set(v___y_2259_, v___x_2290_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6___boxed(lean_object* v_mod_2338_, lean_object* v_isMeta_2339_, lean_object* v_hint_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v_isMeta_boxed_2348_; lean_object* v_res_2349_; 
v_isMeta_boxed_2348_ = lean_unbox(v_isMeta_2339_);
v_res_2349_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6(v_mod_2338_, v_isMeta_boxed_2348_, v_hint_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg(lean_object* v_a_2350_, lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_box(0);
return v___x_2352_;
}
else
{
lean_object* v_key_2353_; lean_object* v_value_2354_; lean_object* v_tail_2355_; uint8_t v___x_2356_; 
v_key_2353_ = lean_ctor_get(v_x_2351_, 0);
v_value_2354_ = lean_ctor_get(v_x_2351_, 1);
v_tail_2355_ = lean_ctor_get(v_x_2351_, 2);
v___x_2356_ = lean_name_eq(v_key_2353_, v_a_2350_);
if (v___x_2356_ == 0)
{
v_x_2351_ = v_tail_2355_;
goto _start;
}
else
{
lean_object* v___x_2358_; 
lean_inc(v_value_2354_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_value_2354_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg___boxed(lean_object* v_a_2359_, lean_object* v_x_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg(v_a_2359_, v_x_2360_);
lean_dec(v_x_2360_);
lean_dec(v_a_2359_);
return v_res_2361_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2362_; uint64_t v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(1723u);
v___x_2363_ = lean_uint64_of_nat(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg(lean_object* v_m_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_buckets_2366_; lean_object* v___x_2367_; uint64_t v___y_2369_; 
v_buckets_2366_ = lean_ctor_get(v_m_2364_, 1);
v___x_2367_ = lean_array_get_size(v_buckets_2366_);
if (lean_obj_tag(v_a_2365_) == 0)
{
uint64_t v___x_2383_; 
v___x_2383_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___closed__0);
v___y_2369_ = v___x_2383_;
goto v___jp_2368_;
}
else
{
uint64_t v_hash_2384_; 
v_hash_2384_ = lean_ctor_get_uint64(v_a_2365_, sizeof(void*)*2);
v___y_2369_ = v_hash_2384_;
goto v___jp_2368_;
}
v___jp_2368_:
{
uint64_t v___x_2370_; uint64_t v___x_2371_; uint64_t v_fold_2372_; uint64_t v___x_2373_; uint64_t v___x_2374_; uint64_t v___x_2375_; size_t v___x_2376_; size_t v___x_2377_; size_t v___x_2378_; size_t v___x_2379_; size_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2370_ = 32ULL;
v___x_2371_ = lean_uint64_shift_right(v___y_2369_, v___x_2370_);
v_fold_2372_ = lean_uint64_xor(v___y_2369_, v___x_2371_);
v___x_2373_ = 16ULL;
v___x_2374_ = lean_uint64_shift_right(v_fold_2372_, v___x_2373_);
v___x_2375_ = lean_uint64_xor(v_fold_2372_, v___x_2374_);
v___x_2376_ = lean_uint64_to_usize(v___x_2375_);
v___x_2377_ = lean_usize_of_nat(v___x_2367_);
v___x_2378_ = ((size_t)1ULL);
v___x_2379_ = lean_usize_sub(v___x_2377_, v___x_2378_);
v___x_2380_ = lean_usize_land(v___x_2376_, v___x_2379_);
v___x_2381_ = lean_array_uget_borrowed(v_buckets_2366_, v___x_2380_);
v___x_2382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg(v_a_2365_, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_m_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg(v_m_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_m_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__7(lean_object* v___x_2388_, lean_object* v_declName_2389_, lean_object* v_as_2390_, size_t v_sz_2391_, size_t v_i_2392_, lean_object* v_b_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = lean_usize_dec_lt(v_i_2392_, v_sz_2391_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
lean_dec(v_declName_2389_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v_b_2393_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; lean_object* v_modules_2404_; lean_object* v___x_2405_; lean_object* v_a_2406_; lean_object* v___x_2407_; lean_object* v_toImport_2408_; lean_object* v_module_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2403_ = l_Lean_Environment_header(v___x_2388_);
v_modules_2404_ = lean_ctor_get(v___x_2403_, 3);
lean_inc_ref(v_modules_2404_);
lean_dec_ref(v___x_2403_);
v___x_2405_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2406_ = lean_array_uget_borrowed(v_as_2390_, v_i_2392_);
v___x_2407_ = lean_array_get(v___x_2405_, v_modules_2404_, v_a_2406_);
lean_dec_ref(v_modules_2404_);
v_toImport_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc_ref(v_toImport_2408_);
lean_dec(v___x_2407_);
v_module_2409_ = lean_ctor_get(v_toImport_2408_, 0);
lean_inc(v_module_2409_);
lean_dec_ref(v_toImport_2408_);
v___x_2410_ = 0;
lean_inc(v_declName_2389_);
v___x_2411_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6(v_module_2409_, v___x_2410_, v_declName_2389_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; 
lean_dec_ref(v___x_2411_);
v___x_2412_ = lean_box(0);
v___x_2413_ = ((size_t)1ULL);
v___x_2414_ = lean_usize_add(v_i_2392_, v___x_2413_);
v_i_2392_ = v___x_2414_;
v_b_2393_ = v___x_2412_;
goto _start;
}
else
{
lean_dec(v_declName_2389_);
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__7___boxed(lean_object* v___x_2416_, lean_object* v_declName_2417_, lean_object* v_as_2418_, lean_object* v_sz_2419_, lean_object* v_i_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
size_t v_sz_boxed_2429_; size_t v_i_boxed_2430_; lean_object* v_res_2431_; 
v_sz_boxed_2429_ = lean_unbox_usize(v_sz_2419_);
lean_dec(v_sz_2419_);
v_i_boxed_2430_ = lean_unbox_usize(v_i_2420_);
lean_dec(v_i_2420_);
v_res_2431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__7(v___x_2416_, v_declName_2417_, v_as_2418_, v_sz_boxed_2429_, v_i_boxed_2430_, v_b_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec_ref(v_as_2418_);
lean_dec_ref(v___x_2416_);
return v_res_2431_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__1));
v___x_2435_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__0));
v___x_2436_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_declName_2439_, uint8_t v_isMeta_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; lean_object* v_env_2452_; lean_object* v___y_2454_; lean_object* v___x_2467_; 
v___x_2448_ = lean_st_ref_get(v___y_2446_);
v_env_2452_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_env_2452_);
lean_dec(v___x_2448_);
v___x_2467_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2452_, v_declName_2439_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_dec_ref(v_env_2452_);
lean_dec(v_declName_2439_);
goto v___jp_2449_;
}
else
{
lean_object* v_val_2468_; lean_object* v___x_2469_; lean_object* v_modules_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref(v___x_2467_);
v___x_2469_ = l_Lean_Environment_header(v_env_2452_);
v_modules_2470_ = lean_ctor_get(v___x_2469_, 3);
lean_inc_ref(v_modules_2470_);
lean_dec_ref(v___x_2469_);
v___x_2471_ = lean_array_get_size(v_modules_2470_);
v___x_2472_ = lean_nat_dec_lt(v_val_2468_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v_modules_2470_);
lean_dec(v_val_2468_);
lean_dec_ref(v_env_2452_);
lean_dec(v_declName_2439_);
goto v___jp_2449_;
}
else
{
lean_object* v___x_2473_; lean_object* v_env_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___y_2478_; 
v___x_2473_ = lean_st_ref_get(v___y_2446_);
v_env_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_env_2474_);
lean_dec(v___x_2473_);
v___x_2475_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__2);
v___x_2476_ = lean_array_fget(v_modules_2470_, v_val_2468_);
lean_dec(v_val_2468_);
lean_dec_ref(v_modules_2470_);
if (v_isMeta_2440_ == 0)
{
lean_dec_ref(v_env_2474_);
v___y_2478_ = v_isMeta_2440_;
goto v___jp_2477_;
}
else
{
uint8_t v___x_2489_; 
lean_inc(v_declName_2439_);
v___x_2489_ = l_Lean_isMarkedMeta(v_env_2474_, v_declName_2439_);
if (v___x_2489_ == 0)
{
v___y_2478_ = v_isMeta_2440_;
goto v___jp_2477_;
}
else
{
uint8_t v___x_2490_; 
v___x_2490_ = 0;
v___y_2478_ = v___x_2490_;
goto v___jp_2477_;
}
}
v___jp_2477_:
{
lean_object* v_toImport_2479_; lean_object* v_module_2480_; lean_object* v___x_2481_; 
v_toImport_2479_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_toImport_2479_);
lean_dec(v___x_2476_);
v_module_2480_ = lean_ctor_get(v_toImport_2479_, 0);
lean_inc(v_module_2480_);
lean_dec_ref(v_toImport_2479_);
lean_inc(v_declName_2439_);
v___x_2481_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6(v_module_2480_, v___y_2478_, v_declName_2439_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v___x_2481_);
v___x_2482_ = l_Lean_indirectModUseExt;
v___x_2483_ = lean_box(1);
v___x_2484_ = lean_box(0);
lean_inc_ref(v_env_2452_);
v___x_2485_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2475_, v___x_2482_, v_env_2452_, v___x_2483_, v___x_2484_);
v___x_2486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg(v___x_2485_, v_declName_2439_);
lean_dec(v___x_2485_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___closed__3));
v___y_2454_ = v___x_2487_;
goto v___jp_2453_;
}
else
{
lean_object* v_val_2488_; 
v_val_2488_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2488_);
lean_dec_ref(v___x_2486_);
v___y_2454_ = v_val_2488_;
goto v___jp_2453_;
}
}
else
{
lean_dec_ref(v_env_2452_);
lean_dec(v_declName_2439_);
return v___x_2481_;
}
}
}
}
v___jp_2449_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_box(0);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
v___jp_2453_:
{
lean_object* v___x_2455_; size_t v_sz_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2455_ = lean_box(0);
v_sz_2456_ = lean_array_size(v___y_2454_);
v___x_2457_ = ((size_t)0ULL);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__7(v_env_2452_, v_declName_2439_, v___y_2454_, v_sz_2456_, v___x_2457_, v___x_2455_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec_ref(v___y_2454_);
lean_dec_ref(v_env_2452_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2458_, 0);
lean_dec(v_unused_2466_);
v___x_2460_ = v___x_2458_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v___x_2458_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2455_);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2455_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_declName_2491_, lean_object* v_isMeta_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v_isMeta_boxed_2500_; lean_object* v_res_2501_; 
v_isMeta_boxed_2500_ = lean_unbox(v_isMeta_2492_);
v_res_2501_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_declName_2491_, v_isMeta_boxed_2500_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg(lean_object* v_as_x27_2502_, lean_object* v_b_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
if (lean_obj_tag(v_as_x27_2502_) == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_b_2503_);
return v___x_2511_;
}
else
{
lean_object* v_head_2512_; lean_object* v_tail_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v_head_2512_ = lean_ctor_get(v_as_x27_2502_, 0);
lean_inc(v_head_2512_);
v_tail_2513_ = lean_ctor_get(v_as_x27_2502_, 1);
lean_inc(v_tail_2513_);
lean_dec_ref(v_as_x27_2502_);
v___x_2514_ = 1;
v___x_2515_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_head_2512_, v___x_2514_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref(v___x_2515_);
v___x_2516_ = lean_box(0);
v_as_x27_2502_ = v_tail_2513_;
v_b_2503_ = v___x_2516_;
goto _start;
}
else
{
lean_dec(v_tail_2513_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg___boxed(lean_object* v_as_x27_2518_, lean_object* v_b_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg(v_as_x27_2518_, v_b_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2528_, lean_object* v_options_2529_, lean_object* v_currNamespace_2530_, lean_object* v_openDecls_2531_, lean_object* v_n_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = l_Lean_ResolveName_resolveGlobalName(v_env_2528_, v_options_2529_, v_currNamespace_2530_, v_openDecls_2531_, v_n_2532_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___y_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2537_, lean_object* v_options_2538_, lean_object* v_currNamespace_2539_, lean_object* v_openDecls_2540_, lean_object* v_n_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2537_, v_options_2538_, v_currNamespace_2539_, v_openDecls_2540_, v_n_2541_, v___y_2542_, v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v_options_2538_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_currNamespace_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v_currNamespace_2545_);
lean_ctor_set(v___x_2548_, 1, v___y_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_currNamespace_2549_, v___y_2550_, v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg(lean_object* v_x_2553_, lean_object* v___y_2554_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v_x_2553_, 0);
lean_inc(v_a_2555_);
v___x_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2556_, 0, v_a_2555_);
lean_ctor_set(v___x_2556_, 1, v___y_2554_);
return v___x_2556_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v_x_2553_, 0);
lean_inc(v_a_2557_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_a_2557_);
lean_ctor_set(v___x_2558_, 1, v___y_2554_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg___boxed(lean_object* v_x_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg(v_x_2559_, v___y_2560_);
lean_dec_ref(v_x_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2562_, lean_object* v_stx_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2562_, v_stx_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
if (lean_obj_tag(v_a_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2576_; 
v_a_2568_ = lean_ctor_get(v___x_2566_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; 
v_unused_2577_ = lean_ctor_get(v___x_2566_, 0);
lean_dec(v_unused_2577_);
v___x_2570_ = v___x_2566_;
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = lean_box(0);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_a_2568_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
lean_object* v_val_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2606_; 
v_val_2578_ = lean_ctor_get(v_a_2567_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_a_2567_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2580_ = v_a_2567_;
v_isShared_2581_ = v_isSharedCheck_2606_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_val_2578_);
lean_dec(v_a_2567_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2606_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_snd_2582_; 
v_snd_2582_ = lean_ctor_get(v_val_2578_, 1);
lean_inc(v_snd_2582_);
lean_dec(v_val_2578_);
if (lean_obj_tag(v_snd_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2592_; 
lean_del_object(v___x_2580_);
v_a_2583_ = lean_ctor_get(v___x_2566_, 1);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2566_);
v_a_2584_ = lean_ctor_get(v_snd_2582_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_snd_2582_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2586_ = v_snd_2582_;
v_isShared_2587_ = v_isSharedCheck_2592_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v_snd_2582_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2592_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg(v___x_2589_, v_a_2583_);
lean_dec_ref(v___x_2589_);
return v___x_2590_;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2605_; 
v_a_2593_ = lean_ctor_get(v___x_2566_, 1);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2566_);
v_a_2594_ = lean_ctor_get(v_snd_2582_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_snd_2582_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2596_ = v_snd_2582_;
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v_snd_2582_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v_a_2594_);
v___x_2599_ = v___x_2580_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2601_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2599_);
v___x_2601_ = v___x_2596_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg(v___x_2601_, v_a_2593_);
lean_dec_ref(v___x_2601_);
return v___x_2602_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2607_ = lean_ctor_get(v___x_2566_, 0);
v_a_2608_ = lean_ctor_get(v___x_2566_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2566_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_inc(v_a_2607_);
lean_dec(v___x_2566_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2607_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2616_, lean_object* v_stx_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2616_, v_stx_2617_, v___y_2618_, v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; lean_object* v_env_2631_; lean_object* v_options_2632_; lean_object* v_currRecDepth_2633_; lean_object* v_maxRecDepth_2634_; lean_object* v_ref_2635_; lean_object* v_currNamespace_2636_; lean_object* v_openDecls_2637_; lean_object* v_quotContext_2638_; lean_object* v_currMacroScope_2639_; lean_object* v___x_2640_; lean_object* v_nextMacroScope_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v_methods_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2630_ = lean_st_ref_get(v___y_2628_);
v_env_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc_ref(v_env_2631_);
lean_dec(v___x_2630_);
v_options_2632_ = lean_ctor_get(v___y_2627_, 2);
v_currRecDepth_2633_ = lean_ctor_get(v___y_2627_, 3);
v_maxRecDepth_2634_ = lean_ctor_get(v___y_2627_, 4);
v_ref_2635_ = lean_ctor_get(v___y_2627_, 5);
v_currNamespace_2636_ = lean_ctor_get(v___y_2627_, 6);
v_openDecls_2637_ = lean_ctor_get(v___y_2627_, 7);
v_quotContext_2638_ = lean_ctor_get(v___y_2627_, 10);
v_currMacroScope_2639_ = lean_ctor_get(v___y_2627_, 11);
v___x_2640_ = lean_st_ref_get(v___y_2628_);
v_nextMacroScope_2641_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_nextMacroScope_2641_);
lean_dec(v___x_2640_);
lean_inc_ref(v_env_2631_);
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2642_, 0, v_env_2631_);
lean_inc_ref(v_env_2631_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2643_, 0, v_env_2631_);
lean_inc(v_openDecls_2637_);
lean_inc(v_currNamespace_2636_);
lean_inc_ref(v_env_2631_);
v___f_2644_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2644_, 0, v_env_2631_);
lean_closure_set(v___f_2644_, 1, v_currNamespace_2636_);
lean_closure_set(v___f_2644_, 2, v_openDecls_2637_);
lean_inc(v_currNamespace_2636_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2645_, 0, v_currNamespace_2636_);
lean_inc(v_openDecls_2637_);
lean_inc(v_currNamespace_2636_);
lean_inc_ref(v_options_2632_);
v___f_2646_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2646_, 0, v_env_2631_);
lean_closure_set(v___f_2646_, 1, v_options_2632_);
lean_closure_set(v___f_2646_, 2, v_currNamespace_2636_);
lean_closure_set(v___f_2646_, 3, v_openDecls_2637_);
v_methods_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2647_, 0, v___f_2642_);
lean_ctor_set(v_methods_2647_, 1, v___f_2645_);
lean_ctor_set(v_methods_2647_, 2, v___f_2643_);
lean_ctor_set(v_methods_2647_, 3, v___f_2644_);
lean_ctor_set(v_methods_2647_, 4, v___f_2646_);
lean_inc(v_ref_2635_);
lean_inc(v_maxRecDepth_2634_);
lean_inc(v_currRecDepth_2633_);
lean_inc(v_currMacroScope_2639_);
lean_inc(v_quotContext_2638_);
v___x_2648_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2648_, 0, v_methods_2647_);
lean_ctor_set(v___x_2648_, 1, v_quotContext_2638_);
lean_ctor_set(v___x_2648_, 2, v_currMacroScope_2639_);
lean_ctor_set(v___x_2648_, 3, v_currRecDepth_2633_);
lean_ctor_set(v___x_2648_, 4, v_maxRecDepth_2634_);
lean_ctor_set(v___x_2648_, 5, v_ref_2635_);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2650_, 0, v_nextMacroScope_2641_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
lean_ctor_set(v___x_2650_, 2, v___x_2649_);
v___x_2651_ = lean_apply_2(v_x_2622_, v___x_2648_, v___x_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v_a_2653_; lean_object* v_macroScope_2654_; lean_object* v_traceMsgs_2655_; lean_object* v_expandedMacroDecls_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 1);
lean_inc(v_a_2652_);
v_a_2653_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2651_);
v_macroScope_2654_ = lean_ctor_get(v_a_2652_, 0);
lean_inc(v_macroScope_2654_);
v_traceMsgs_2655_ = lean_ctor_get(v_a_2652_, 1);
lean_inc(v_traceMsgs_2655_);
v_expandedMacroDecls_2656_ = lean_ctor_get(v_a_2652_, 2);
lean_inc(v_expandedMacroDecls_2656_);
lean_dec(v_a_2652_);
v___x_2657_ = lean_box(0);
v___x_2658_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg(v_expandedMacroDecls_2656_, v___x_2657_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2659_; lean_object* v_env_2660_; lean_object* v_ngen_2661_; lean_object* v_auxDeclNGen_2662_; lean_object* v_traceState_2663_; lean_object* v_cache_2664_; lean_object* v_messages_2665_; lean_object* v_infoState_2666_; lean_object* v_snapshotTasks_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v___x_2658_);
v___x_2659_ = lean_st_ref_take(v___y_2628_);
v_env_2660_ = lean_ctor_get(v___x_2659_, 0);
v_ngen_2661_ = lean_ctor_get(v___x_2659_, 2);
v_auxDeclNGen_2662_ = lean_ctor_get(v___x_2659_, 3);
v_traceState_2663_ = lean_ctor_get(v___x_2659_, 4);
v_cache_2664_ = lean_ctor_get(v___x_2659_, 5);
v_messages_2665_ = lean_ctor_get(v___x_2659_, 6);
v_infoState_2666_ = lean_ctor_get(v___x_2659_, 7);
v_snapshotTasks_2667_ = lean_ctor_get(v___x_2659_, 8);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2659_, 1);
lean_dec(v_unused_2694_);
v___x_2669_ = v___x_2659_;
v_isShared_2670_ = v_isSharedCheck_2693_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_snapshotTasks_2667_);
lean_inc(v_infoState_2666_);
lean_inc(v_messages_2665_);
lean_inc(v_cache_2664_);
lean_inc(v_traceState_2663_);
lean_inc(v_auxDeclNGen_2662_);
lean_inc(v_ngen_2661_);
lean_inc(v_env_2660_);
lean_dec(v___x_2659_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2693_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v_macroScope_2654_);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_env_2660_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_macroScope_2654_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_ngen_2661_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_auxDeclNGen_2662_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v_traceState_2663_);
lean_ctor_set(v_reuseFailAlloc_2692_, 5, v_cache_2664_);
lean_ctor_set(v_reuseFailAlloc_2692_, 6, v_messages_2665_);
lean_ctor_set(v_reuseFailAlloc_2692_, 7, v_infoState_2666_);
lean_ctor_set(v_reuseFailAlloc_2692_, 8, v_snapshotTasks_2667_);
v___x_2672_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_st_ref_set(v___y_2628_, v___x_2672_);
v___x_2674_ = l_List_reverse___redArg(v_traceMsgs_2655_);
v___x_2675_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v___x_2674_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2623_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v___x_2675_, 0);
lean_dec(v_unused_2683_);
v___x_2677_ = v___x_2675_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v___x_2675_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v_a_2653_);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2653_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_a_2653_);
v_a_2684_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2675_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2675_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_traceMsgs_2655_);
lean_dec(v_macroScope_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2623_);
v_a_2695_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2658_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2658_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2651_);
if (lean_obj_tag(v_a_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v_a_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_a_2704_ = lean_ctor_get(v_a_2703_, 0);
lean_inc(v_a_2704_);
v_a_2705_ = lean_ctor_get(v_a_2703_, 1);
lean_inc_ref(v_a_2705_);
lean_dec_ref(v_a_2703_);
v___x_2706_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2707_ = lean_string_dec_eq(v_a_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2705_);
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
v___x_2710_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2704_, v___x_2709_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v_a_2704_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; 
lean_dec_ref(v_a_2705_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2623_);
v___x_2711_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg(v_a_2704_);
return v___x_2711_;
}
}
else
{
lean_object* v___x_2712_; 
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2623_);
v___x_2712_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
return v_res_2721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_box(0);
v___x_2726_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2727_ = l_Lean_mkConst(v___x_2726_, v___x_2725_);
return v___x_2727_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2730_ = l_Lean_stringToMessageData(v___x_2729_);
return v___x_2730_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2738_ = l_Lean_mkConst(v___x_2737_, v___x_2736_);
return v___x_2738_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2741_, lean_object* v_as_2742_, size_t v_sz_2743_, size_t v_i_2744_, lean_object* v_b_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_a_2754_; uint8_t v___x_2758_; 
v___x_2758_ = lean_usize_dec_lt(v_i_2744_, v_sz_2743_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; 
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_b_2745_);
return v___x_2759_;
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v_a_2762_; uint8_t v___x_2763_; 
v___x_2760_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2761_ = lean_box(0);
v_a_2762_ = lean_array_uget_borrowed(v_as_2742_, v_i_2744_);
lean_inc(v_a_2762_);
v___x_2763_ = l_Lean_Syntax_isOfKind(v_a_2762_, v___x_2760_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_dec_ref(v___x_2764_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2764_;
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = lean_unsigned_to_nat(1u);
v___x_2767_ = l_Lean_Syntax_getArg(v_a_2762_, v___x_2765_);
v___x_2768_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2767_);
v___x_2769_ = l_Lean_Syntax_isOfKind(v___x_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2767_);
v___x_2771_ = l_Lean_Syntax_isOfKind(v___x_2767_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; 
lean_dec(v___x_2767_);
v___x_2772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_dec_ref(v___x_2772_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2772_;
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = l_Lean_Syntax_getArg(v___x_2767_, v___x_2765_);
v___x_2774_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2773_);
v___x_2775_ = l_Lean_Syntax_isOfKind(v___x_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; 
lean_dec(v___x_2773_);
lean_dec(v___x_2767_);
v___x_2776_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref(v___x_2776_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2776_;
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2777_ = l_Lean_Syntax_getArg(v___x_2767_, v___x_2766_);
lean_dec(v___x_2767_);
v___x_2778_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2777_);
v___x_2779_ = l_Lean_Syntax_isOfKind(v___x_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec(v___x_2777_);
lean_dec(v___x_2773_);
v___x_2780_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_dec_ref(v___x_2780_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2780_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2781_, 0, v___x_2773_);
lean_inc_ref(v___y_2750_);
lean_inc_ref(v___y_2746_);
v___x_2782_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2781_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___x_2784_ = l_Lean_Widget_elabWidgetInstanceSpec(v___x_2777_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v_a_2785_);
v___x_2786_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2785_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2786_) == 0)
{
uint8_t v___x_2787_; 
v___x_2787_ = lean_unbox(v_a_2783_);
if (v___x_2787_ == 1)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
lean_dec(v_a_2785_);
lean_dec(v_a_2783_);
v_a_2788_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2786_);
v___x_2789_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2788_, v___y_2749_, v___y_2751_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref(v___x_2789_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2789_;
}
}
else
{
lean_object* v_a_2790_; lean_object* v_id_2791_; uint64_t v_javascriptHash_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2790_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2786_);
v_id_2791_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_id_2791_);
v_javascriptHash_2792_ = lean_ctor_get_uint64(v_a_2790_, sizeof(void*)*2);
lean_dec(v_a_2790_);
v___x_2793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1));
v___x_2794_ = l_Lean_Name_append(v_id_2791_, v___x_2793_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
v___x_2795_ = l_Lean_Core_mkFreshUserName(v___x_2794_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2797_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
v___x_2797_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2785_, v___y_2749_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___x_2818_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = lean_box(0);
v___x_2818_ = l_Lean_Expr_hasMVar(v_a_2798_);
if (v___x_2818_ == 0)
{
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___y_2801_ = v___y_2746_;
v___y_2802_ = v___y_2747_;
v___y_2803_ = v___y_2748_;
v___y_2804_ = v___y_2749_;
v___y_2805_ = v___y_2750_;
v___y_2806_ = v___y_2751_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2798_);
v___x_2820_ = l_Lean_indentExpr(v_a_2798_);
v___x_2821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
lean_inc_ref(v___y_2746_);
v___x_2822_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2821_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_dec_ref(v___x_2822_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___y_2801_ = v___y_2746_;
v___y_2802_ = v___y_2747_;
v___y_2803_ = v___y_2748_;
v___y_2804_ = v___y_2749_;
v___y_2805_ = v___y_2750_;
v___y_2806_ = v___y_2751_;
goto v___jp_2800_;
}
else
{
lean_dec(v_a_2798_);
lean_dec(v_a_2796_);
lean_dec(v_a_2783_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2822_;
}
}
v___jp_2800_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
lean_inc(v_a_2796_);
v___x_2808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2808_, 0, v_a_2796_);
lean_ctor_set(v___x_2808_, 1, v___x_2799_);
lean_ctor_set(v___x_2808_, 2, v___x_2807_);
v___x_2809_ = lean_box(0);
v___x_2810_ = 1;
lean_inc(v_a_2796_);
v___x_2811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2796_);
lean_ctor_set(v___x_2811_, 1, v___x_2799_);
v___x_2812_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2812_, 0, v___x_2808_);
lean_ctor_set(v___x_2812_, 1, v_a_2798_);
lean_ctor_set(v___x_2812_, 2, v___x_2809_);
lean_ctor_set(v___x_2812_, 3, v___x_2811_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*4, v___x_2810_);
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_inc(v___y_2806_);
lean_inc_ref(v___y_2805_);
v___x_2814_ = l_Lean_addAndCompile(v___x_2813_, v___x_2741_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2814_) == 0)
{
uint8_t v___x_2815_; 
lean_dec_ref(v___x_2814_);
v___x_2815_ = lean_unbox(v_a_2783_);
lean_dec(v_a_2783_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_2792_, v_a_2796_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_dec_ref(v___x_2816_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2816_;
}
}
else
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_2792_, v_a_2796_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_dec_ref(v___x_2817_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2817_;
}
}
}
else
{
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v_a_2796_);
lean_dec(v_a_2783_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2783_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2823_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2797_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2797_);
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
lean_dec(v_a_2785_);
lean_dec(v_a_2783_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2831_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2795_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2795_);
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
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_a_2785_);
lean_dec(v_a_2783_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2839_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2786_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2786_);
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
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2783_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2847_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2784_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2784_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v___x_2777_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2855_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2782_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2782_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = l_Lean_Syntax_getArg(v___x_2767_, v___x_2766_);
lean_dec(v___x_2767_);
v___x_2864_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2863_);
v___x_2865_ = l_Lean_Syntax_isOfKind(v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v___x_2863_);
v___x_2866_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_dec_ref(v___x_2866_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2866_;
}
}
else
{
lean_object* v_ref_2867_; lean_object* v_quotContext_2868_; lean_object* v_currMacroScope_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_ref_2867_ = lean_ctor_get(v___y_2750_, 5);
v_quotContext_2868_ = lean_ctor_get(v___y_2750_, 10);
v_currMacroScope_2869_ = lean_ctor_get(v___y_2750_, 11);
v___x_2870_ = 0;
v___x_2871_ = l_Lean_SourceInfo_fromRef(v_ref_2867_, v___x_2870_);
v___x_2872_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2873_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2874_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2869_);
lean_inc(v_quotContext_2868_);
v___x_2875_ = l_Lean_addMacroScope(v_quotContext_2868_, v___x_2874_, v_currMacroScope_2869_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc(v___x_2871_);
v___x_2877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2871_);
lean_ctor_set(v___x_2877_, 1, v___x_2873_);
lean_ctor_set(v___x_2877_, 2, v___x_2875_);
lean_ctor_set(v___x_2877_, 3, v___x_2876_);
v___x_2878_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
lean_inc(v___x_2871_);
v___x_2879_ = l_Lean_Syntax_node1(v___x_2871_, v___x_2878_, v___x_2863_);
v___x_2880_ = l_Lean_Syntax_node2(v___x_2871_, v___x_2872_, v___x_2877_, v___x_2879_);
v___x_2881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___x_2882_ = l_Lean_Elab_Term_elabTerm(v___x_2880_, v___x_2881_, v___x_2741_, v___x_2741_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
v___x_2884_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2883_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; uint64_t v_javascriptHash_2886_; lean_object* v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref(v___x_2884_);
v_javascriptHash_2886_ = lean_ctor_get_uint64(v_a_2885_, sizeof(void*)*1);
lean_dec(v_a_2885_);
v___x_2887_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2886_, v___y_2749_, v___y_2751_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_dec_ref(v___x_2887_);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v___x_2887_;
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2888_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2884_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2884_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
v_a_2896_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2882_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2882_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
}
v___jp_2753_:
{
size_t v___x_2755_; size_t v___x_2756_; 
v___x_2755_ = ((size_t)1ULL);
v___x_2756_ = lean_usize_add(v_i_2744_, v___x_2755_);
v_i_2744_ = v___x_2756_;
v_b_2745_ = v_a_2754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2904_, lean_object* v_as_2905_, lean_object* v_sz_2906_, lean_object* v_i_2907_, lean_object* v_b_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
uint8_t v___x_34556__boxed_2916_; size_t v_sz_boxed_2917_; size_t v_i_boxed_2918_; lean_object* v_res_2919_; 
v___x_34556__boxed_2916_ = lean_unbox(v___x_2904_);
v_sz_boxed_2917_ = lean_unbox_usize(v_sz_2906_);
lean_dec(v_sz_2906_);
v_i_boxed_2918_ = lean_unbox_usize(v_i_2907_);
lean_dec(v_i_2907_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_34556__boxed_2916_, v_as_2905_, v_sz_boxed_2917_, v_i_boxed_2918_, v_b_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec_ref(v_as_2905_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2920_, lean_object* v___x_2921_, size_t v_sz_2922_, size_t v___x_2923_, lean_object* v___x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2920_, v___x_2921_, v_sz_2922_, v___x_2923_, v___x_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v___x_2932_, 0);
lean_dec(v_unused_2940_);
v___x_2934_ = v___x_2932_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_dec(v___x_2932_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2924_);
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2924_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_2941_, lean_object* v___x_2942_, lean_object* v_sz_2943_, lean_object* v___x_2944_, lean_object* v___x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v___x_34908__boxed_2953_; size_t v_sz_boxed_2954_; size_t v___x_34910__boxed_2955_; lean_object* v_res_2956_; 
v___x_34908__boxed_2953_ = lean_unbox(v___x_2941_);
v_sz_boxed_2954_ = lean_unbox_usize(v_sz_2943_);
lean_dec(v_sz_2943_);
v___x_34910__boxed_2955_ = lean_unbox_usize(v___x_2944_);
lean_dec(v___x_2944_);
v_res_2956_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_34908__boxed_2953_, v___x_2942_, v_sz_boxed_2954_, v___x_34910__boxed_2955_, v___x_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec_ref(v___x_2942_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_2959_);
v___x_2964_ = l_Lean_Syntax_isOfKind(v_x_2959_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref(v_a_2960_);
lean_dec(v_x_2959_);
v___x_2965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v_ws_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; size_t v_sz_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; 
v___x_2966_ = lean_unsigned_to_nat(2u);
v___x_2967_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2966_);
lean_dec(v_x_2959_);
v_ws_2968_ = l_Lean_Syntax_getArgs(v___x_2967_);
lean_dec(v___x_2967_);
v___x_2969_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_2968_);
lean_dec_ref(v_ws_2968_);
v___x_2970_ = lean_box(0);
v_sz_2971_ = lean_array_size(v___x_2969_);
v___x_2972_ = lean_box(v___x_2964_);
v___x_2973_ = lean_box_usize(v_sz_2971_);
v___x_2974_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2975_, 0, v___x_2972_);
lean_closure_set(v___f_2975_, 1, v___x_2969_);
lean_closure_set(v___f_2975_, 2, v___x_2973_);
lean_closure_set(v___f_2975_, 3, v___x_2974_);
lean_closure_set(v___f_2975_, 4, v___x_2970_);
v___x_2976_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2975_, v_a_2960_, v_a_2961_);
return v___x_2976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_2977_, v_a_2978_, v_a_2979_);
lean_dec(v_a_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2982_, v___y_2987_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_00_u03b1_3000_, lean_object* v_x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___redArg(v_x_3001_, v___y_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3005_, lean_object* v_x_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_00_u03b1_3005_, v_x_3006_, v___y_3007_, v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v_x_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8(lean_object* v_00_u03b1_3010_, lean_object* v_ref_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___redArg(v_ref_3011_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3020_, lean_object* v_ref_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__8(v_00_u03b1_3020_, v_ref_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3030_, lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3040_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3050_, v___y_3054_, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(lean_object* v_00_u03b1_3068_, lean_object* v_00_u03b2_3069_, lean_object* v_00_u03c3_3070_, lean_object* v_ext_3071_, lean_object* v_b_3072_, uint8_t v_kind_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___redArg(v_ext_3071_, v_b_3072_, v_kind_3073_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14___boxed(lean_object* v_00_u03b1_3082_, lean_object* v_00_u03b2_3083_, lean_object* v_00_u03c3_3084_, lean_object* v_ext_3085_, lean_object* v_b_3086_, lean_object* v_kind_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
uint8_t v_kind_boxed_3095_; lean_object* v_res_3096_; 
v_kind_boxed_3095_ = lean_unbox(v_kind_3087_);
v_res_3096_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__14(v_00_u03b1_3082_, v_00_u03b2_3083_, v_00_u03c3_3084_, v_ext_3085_, v_b_3086_, v_kind_boxed_3095_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3097_, lean_object* v_msg_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3107_, lean_object* v_msg_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3107_, v_msg_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3117_, v___y_3121_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
uint64_t v_h_boxed_3134_; lean_object* v_res_3135_; 
v_h_boxed_3134_ = lean_unbox_uint64(v_h_3126_);
lean_dec_ref(v_h_3126_);
v_res_3135_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3134_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_cls_3136_, lean_object* v_msg_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_cls_3136_, v_msg_3137_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_cls_3146_, lean_object* v_msg_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_cls_3146_, v_msg_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_3156_, lean_object* v_as_x27_3157_, lean_object* v_b_3158_, lean_object* v_a_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___redArg(v_as_x27_3157_, v_b_3158_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_3168_, lean_object* v_as_x27_3169_, lean_object* v_b_3170_, lean_object* v_a_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_3168_, v_as_x27_3169_, v_b_3170_, v_a_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v_as_3168_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_3180_, lean_object* v_ref_3181_, lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_3181_, v_msg_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3191_, lean_object* v_ref_3192_, lean_object* v_msg_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3191_, v_ref_3192_, v_msg_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec(v_ref_3192_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b4_3202_, lean_object* v_t_3203_, uint64_t v_k_3204_, lean_object* v_fallback_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_t_3203_, v_k_3204_, v_fallback_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b4_3207_, lean_object* v_t_3208_, lean_object* v_k_3209_, lean_object* v_fallback_3210_){
_start:
{
uint64_t v_k_boxed_3211_; lean_object* v_res_3212_; 
v_k_boxed_3211_ = lean_unbox_uint64(v_k_3209_);
lean_dec_ref(v_k_3209_);
v_res_3212_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b4_3207_, v_t_3208_, v_k_boxed_3211_, v_fallback_3210_);
lean_dec(v_fallback_3210_);
lean_dec(v_t_3208_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11(lean_object* v_00_u03b2_3213_, uint64_t v_k_3214_, lean_object* v_v_3215_, lean_object* v_t_3216_, lean_object* v_hl_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___redArg(v_k_3214_, v_v_3215_, v_t_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11___boxed(lean_object* v_00_u03b2_3219_, lean_object* v_k_3220_, lean_object* v_v_3221_, lean_object* v_t_3222_, lean_object* v_hl_3223_){
_start:
{
uint64_t v_k_boxed_3224_; lean_object* v_res_3225_; 
v_k_boxed_3224_ = lean_unbox_uint64(v_k_3220_);
lean_dec_ref(v_k_3220_);
v_res_3225_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__11(v_00_u03b2_3219_, v_k_boxed_3224_, v_v_3221_, v_t_3222_, v_hl_3223_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(lean_object* v_msgData_3226_, lean_object* v_macroStack_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___redArg(v_msgData_3226_, v_macroStack_3227_, v___y_3232_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18___boxed(lean_object* v_msgData_3236_, lean_object* v_macroStack_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__18(v_msgData_3236_, v_macroStack_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(lean_object* v_00_u03b2_3246_, uint64_t v_k_3247_, lean_object* v_t_3248_, lean_object* v_h_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___redArg(v_k_3247_, v_t_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20___boxed(lean_object* v_00_u03b2_3251_, lean_object* v_k_3252_, lean_object* v_t_3253_, lean_object* v_h_3254_){
_start:
{
uint64_t v_k_boxed_3255_; lean_object* v_res_3256_; 
v_k_boxed_3255_ = lean_unbox_uint64(v_k_3252_);
lean_dec_ref(v_k_3252_);
v_res_3256_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__20(v_00_u03b2_3251_, v_k_boxed_3255_, v_t_3253_, v_h_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_3257_, lean_object* v_m_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___redArg(v_m_3258_, v_a_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3261_, lean_object* v_m_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8(v_00_u03b2_3261_, v_m_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_m_3262_);
return v_res_3264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16(lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___redArg(v_x_3266_, v_x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
uint8_t v_res_3272_; lean_object* v_r_3273_; 
v_res_3272_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16(v_00_u03b2_3269_, v_x_3270_, v_x_3271_);
lean_dec_ref(v_x_3271_);
v_r_3273_ = lean_box(v_res_3272_);
return v_r_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19(lean_object* v_00_u03b2_3274_, lean_object* v_a_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___redArg(v_a_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_a_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__8_spec__19(v_00_u03b2_3278_, v_a_3279_, v_x_3280_);
lean_dec(v_x_3280_);
lean_dec(v_a_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25(lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, size_t v_x_3284_, lean_object* v_x_3285_){
_start:
{
uint8_t v___x_3286_; 
v___x_3286_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___redArg(v_x_3283_, v_x_3284_, v_x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25___boxed(lean_object* v_00_u03b2_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
size_t v_x_35301__boxed_3291_; uint8_t v_res_3292_; lean_object* v_r_3293_; 
v_x_35301__boxed_3291_ = lean_unbox_usize(v_x_3289_);
lean_dec(v_x_3289_);
v_res_3292_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25(v_00_u03b2_3287_, v_x_3288_, v_x_35301__boxed_3291_, v_x_3290_);
lean_dec_ref(v_x_3290_);
v_r_3293_ = lean_box(v_res_3292_);
return v_r_3293_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29(lean_object* v_00_u03b2_3294_, lean_object* v_keys_3295_, lean_object* v_vals_3296_, lean_object* v_heq_3297_, lean_object* v_i_3298_, lean_object* v_k_3299_){
_start:
{
uint8_t v___x_3300_; 
v___x_3300_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___redArg(v_keys_3295_, v_i_3298_, v_k_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29___boxed(lean_object* v_00_u03b2_3301_, lean_object* v_keys_3302_, lean_object* v_vals_3303_, lean_object* v_heq_3304_, lean_object* v_i_3305_, lean_object* v_k_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4_spec__6_spec__16_spec__25_spec__29(v_00_u03b2_3301_, v_keys_3302_, v_vals_3303_, v_heq_3304_, v_i_3305_, v_k_3306_);
lean_dec_ref(v_k_3306_);
lean_dec_ref(v_vals_3303_);
lean_dec_ref(v_keys_3302_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; 
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
v___x_3335_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3326_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
v___x_3337_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3336_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; uint64_t v_javascriptHash_3339_; lean_object* v_props_3340_; lean_object* v___x_3341_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
v_javascriptHash_3339_ = lean_ctor_get_uint64(v_a_3338_, sizeof(void*)*2);
v_props_3340_ = lean_ctor_get(v_a_3338_, 1);
lean_inc_ref(v_props_3340_);
lean_dec(v_a_3338_);
v___x_3341_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3339_, v_props_3340_, v_x_3327_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
return v___x_3341_;
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v_x_3327_);
v_a_3342_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3337_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3337_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v_x_3327_);
v_a_3350_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3335_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3335_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3358_, v_x_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3368_);
v___x_3373_ = l_Lean_Syntax_isOfKind(v_x_3368_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
lean_dec_ref(v_a_3369_);
lean_dec(v_x_3368_);
v___x_3374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3374_;
}
else
{
lean_object* v___x_3375_; lean_object* v_s_3376_; lean_object* v___f_3377_; lean_object* v___x_3378_; 
v___x_3375_ = lean_unsigned_to_nat(1u);
v_s_3376_ = l_Lean_Syntax_getArg(v_x_3368_, v___x_3375_);
v___f_3377_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3377_, 0, v_s_3376_);
lean_closure_set(v___f_3377_, 1, v_x_3368_);
v___x_3378_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3377_, v_a_3369_, v_a_3370_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Widget_elabWidgetCmd(v_x_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
return v_res_3383_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_Commands(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
