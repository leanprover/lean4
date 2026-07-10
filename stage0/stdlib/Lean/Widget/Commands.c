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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0;
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
uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = l_Lean_Expr_hasMVar(v_e_562_);
v___x_566_ = lean_bool_not(v___x_565_);
if (v___x_566_ == 0)
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
v___x_582_ = lean_st_ref_set(v___y_563_, v___x_581_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_fst_570_);
return v___x_583_;
}
}
}
else
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_e_562_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(lean_object* v_e_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_588_, v___y_589_);
lean_dec(v___y_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(lean_object* v_e_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_e_592_, v___y_596_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(lean_object* v_e_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(v_e_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(uint64_t v_k_610_, lean_object* v_t_611_){
_start:
{
if (lean_obj_tag(v_t_611_) == 0)
{
lean_object* v_k_612_; lean_object* v_v_613_; lean_object* v_l_614_; lean_object* v_r_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_1272_; 
v_k_612_ = lean_ctor_get(v_t_611_, 1);
v_v_613_ = lean_ctor_get(v_t_611_, 2);
v_l_614_ = lean_ctor_get(v_t_611_, 3);
v_r_615_ = lean_ctor_get(v_t_611_, 4);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_t_611_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v_t_611_, 0);
lean_dec(v_unused_1273_);
v___x_617_ = v_t_611_;
v_isShared_618_ = v_isSharedCheck_1272_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_r_615_);
lean_inc(v_l_614_);
lean_inc(v_v_613_);
lean_inc(v_k_612_);
lean_dec(v_t_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_1272_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint64_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_unbox_uint64(v_k_612_);
v___x_620_ = lean_uint64_dec_lt(v_k_610_, v___x_619_);
if (v___x_620_ == 0)
{
uint64_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_unbox_uint64(v_k_612_);
v___x_622_ = lean_uint64_dec_eq(v_k_610_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v_impl_623_; lean_object* v___x_624_; 
v_impl_623_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_610_, v_r_615_);
v___x_624_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_623_) == 0)
{
if (lean_obj_tag(v_l_614_) == 0)
{
lean_object* v_size_625_; lean_object* v_size_626_; lean_object* v_k_627_; lean_object* v_v_628_; lean_object* v_l_629_; lean_object* v_r_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_size_625_ = lean_ctor_get(v_impl_623_, 0);
lean_inc(v_size_625_);
v_size_626_ = lean_ctor_get(v_l_614_, 0);
v_k_627_ = lean_ctor_get(v_l_614_, 1);
v_v_628_ = lean_ctor_get(v_l_614_, 2);
v_l_629_ = lean_ctor_get(v_l_614_, 3);
v_r_630_ = lean_ctor_get(v_l_614_, 4);
lean_inc(v_r_630_);
v___x_631_ = lean_unsigned_to_nat(3u);
v___x_632_ = lean_nat_mul(v___x_631_, v_size_625_);
v___x_633_ = lean_nat_dec_lt(v___x_632_, v_size_626_);
lean_dec(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec(v_r_630_);
v___x_634_ = lean_nat_add(v___x_624_, v_size_626_);
v___x_635_ = lean_nat_add(v___x_634_, v_size_625_);
lean_dec(v_size_625_);
lean_dec(v___x_634_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_impl_623_);
lean_ctor_set(v___x_617_, 0, v___x_635_);
v___x_637_ = v___x_617_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_l_614_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_impl_623_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_704_; 
lean_inc(v_l_629_);
lean_inc(v_v_628_);
lean_inc(v_k_627_);
lean_inc(v_size_626_);
v_isSharedCheck_704_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_705_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_l_614_, 2);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_l_614_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_709_);
v___x_640_ = v_l_614_;
v_isShared_641_ = v_isSharedCheck_704_;
goto v_resetjp_639_;
}
else
{
lean_dec(v_l_614_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_704_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_size_642_; lean_object* v_size_643_; lean_object* v_k_644_; lean_object* v_v_645_; lean_object* v_l_646_; lean_object* v_r_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_size_642_ = lean_ctor_get(v_l_629_, 0);
v_size_643_ = lean_ctor_get(v_r_630_, 0);
v_k_644_ = lean_ctor_get(v_r_630_, 1);
v_v_645_ = lean_ctor_get(v_r_630_, 2);
v_l_646_ = lean_ctor_get(v_r_630_, 3);
v_r_647_ = lean_ctor_get(v_r_630_, 4);
v___x_648_ = lean_unsigned_to_nat(2u);
v___x_649_ = lean_nat_mul(v___x_648_, v_size_642_);
v___x_650_ = lean_nat_dec_lt(v_size_643_, v___x_649_);
lean_dec(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_679_; 
lean_inc(v_r_647_);
lean_inc(v_l_646_);
lean_inc(v_v_645_);
lean_inc(v_k_644_);
v_isSharedCheck_679_ = !lean_is_exclusive(v_r_630_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_680_ = lean_ctor_get(v_r_630_, 4);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_r_630_, 3);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_r_630_, 2);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_630_, 1);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_r_630_, 0);
lean_dec(v_unused_684_);
v___x_652_ = v_r_630_;
v_isShared_653_ = v_isSharedCheck_679_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_r_630_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_679_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___x_667_; lean_object* v___y_669_; 
v___x_654_ = lean_nat_add(v___x_624_, v_size_626_);
lean_dec(v_size_626_);
v___x_655_ = lean_nat_add(v___x_654_, v_size_625_);
lean_dec(v___x_654_);
v___x_667_ = lean_nat_add(v___x_624_, v_size_642_);
if (lean_obj_tag(v_l_646_) == 0)
{
lean_object* v_size_677_; 
v_size_677_ = lean_ctor_get(v_l_646_, 0);
lean_inc(v_size_677_);
v___y_669_ = v_size_677_;
goto v___jp_668_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_unsigned_to_nat(0u);
v___y_669_ = v___x_678_;
goto v___jp_668_;
}
v___jp_656_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_nat_add(v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 4, v_impl_623_);
lean_ctor_set(v___x_652_, 3, v_r_647_);
lean_ctor_set(v___x_652_, 2, v_v_613_);
lean_ctor_set(v___x_652_, 1, v_k_612_);
lean_ctor_set(v___x_652_, 0, v___x_660_);
v___x_662_ = v___x_652_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v_r_647_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v_impl_623_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v___x_662_);
lean_ctor_set(v___x_640_, 3, v___y_657_);
lean_ctor_set(v___x_640_, 2, v_v_645_);
lean_ctor_set(v___x_640_, 1, v_k_644_);
lean_ctor_set(v___x_640_, 0, v___x_655_);
v___x_664_ = v___x_640_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_644_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_645_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v___y_657_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_nat_add(v___x_667_, v___y_669_);
lean_dec(v___y_669_);
lean_dec(v___x_667_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_l_646_);
lean_ctor_set(v___x_617_, 3, v_l_629_);
lean_ctor_set(v___x_617_, 2, v_v_628_);
lean_ctor_set(v___x_617_, 1, v_k_627_);
lean_ctor_set(v___x_617_, 0, v___x_670_);
v___x_672_ = v___x_617_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_l_629_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_l_646_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; 
v___x_673_ = lean_nat_add(v___x_624_, v_size_625_);
lean_dec(v_size_625_);
if (lean_obj_tag(v_r_647_) == 0)
{
lean_object* v_size_674_; 
v_size_674_ = lean_ctor_get(v_r_647_, 0);
lean_inc(v_size_674_);
v___y_657_ = v___x_672_;
v___y_658_ = v___x_673_;
v___y_659_ = v_size_674_;
goto v___jp_656_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___y_657_ = v___x_672_;
v___y_658_ = v___x_673_;
v___y_659_ = v___x_675_;
goto v___jp_656_;
}
}
}
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
lean_del_object(v___x_617_);
v___x_685_ = lean_nat_add(v___x_624_, v_size_626_);
lean_dec(v_size_626_);
v___x_686_ = lean_nat_add(v___x_685_, v_size_625_);
lean_dec(v___x_685_);
v___x_687_ = lean_nat_add(v___x_624_, v_size_625_);
lean_dec(v_size_625_);
v___x_688_ = lean_nat_add(v___x_687_, v_size_643_);
lean_dec(v___x_687_);
lean_inc_ref(v_impl_623_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_impl_623_);
lean_ctor_set(v___x_640_, 3, v_r_630_);
lean_ctor_set(v___x_640_, 2, v_v_613_);
lean_ctor_set(v___x_640_, 1, v_k_612_);
lean_ctor_set(v___x_640_, 0, v___x_688_);
v___x_690_ = v___x_640_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_r_630_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_impl_623_);
v___x_690_ = v_reuseFailAlloc_703_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_isSharedCheck_697_ = !lean_is_exclusive(v_impl_623_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; 
v_unused_698_ = lean_ctor_get(v_impl_623_, 4);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_impl_623_, 3);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_impl_623_, 2);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_impl_623_, 1);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_impl_623_, 0);
lean_dec(v_unused_702_);
v___x_692_ = v_impl_623_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_dec(v_impl_623_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 4, v___x_690_);
lean_ctor_set(v___x_692_, 3, v_l_629_);
lean_ctor_set(v___x_692_, 2, v_v_628_);
lean_ctor_set(v___x_692_, 1, v_k_627_);
lean_ctor_set(v___x_692_, 0, v___x_686_);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_l_629_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v___x_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v_size_710_ = lean_ctor_get(v_impl_623_, 0);
lean_inc(v_size_710_);
v___x_711_ = lean_nat_add(v___x_624_, v_size_710_);
lean_dec(v_size_710_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_impl_623_);
lean_ctor_set(v___x_617_, 0, v___x_711_);
v___x_713_ = v___x_617_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_l_614_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_impl_623_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
if (lean_obj_tag(v_l_614_) == 0)
{
lean_object* v_l_715_; 
v_l_715_ = lean_ctor_get(v_l_614_, 3);
if (lean_obj_tag(v_l_715_) == 0)
{
lean_object* v_r_716_; 
lean_inc_ref(v_l_715_);
v_r_716_ = lean_ctor_get(v_l_614_, 4);
lean_inc(v_r_716_);
if (lean_obj_tag(v_r_716_) == 0)
{
lean_object* v_size_717_; lean_object* v_k_718_; lean_object* v_v_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_732_; 
v_size_717_ = lean_ctor_get(v_l_614_, 0);
v_k_718_ = lean_ctor_get(v_l_614_, 1);
v_v_719_ = lean_ctor_get(v_l_614_, 2);
v_isSharedCheck_732_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; lean_object* v_unused_734_; 
v_unused_733_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_734_);
v___x_721_ = v_l_614_;
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_v_719_);
lean_inc(v_k_718_);
lean_inc(v_size_717_);
lean_dec(v_l_614_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_size_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v_size_723_ = lean_ctor_get(v_r_716_, 0);
v___x_724_ = lean_nat_add(v___x_624_, v_size_717_);
lean_dec(v_size_717_);
v___x_725_ = lean_nat_add(v___x_624_, v_size_723_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 4, v_impl_623_);
lean_ctor_set(v___x_721_, 3, v_r_716_);
lean_ctor_set(v___x_721_, 2, v_v_613_);
lean_ctor_set(v___x_721_, 1, v_k_612_);
lean_ctor_set(v___x_721_, 0, v___x_725_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_r_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_impl_623_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_727_);
lean_ctor_set(v___x_617_, 3, v_l_715_);
lean_ctor_set(v___x_617_, 2, v_v_719_);
lean_ctor_set(v___x_617_, 1, v_k_718_);
lean_ctor_set(v___x_617_, 0, v___x_724_);
v___x_729_ = v___x_617_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_l_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_k_735_; lean_object* v_v_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_747_; 
v_k_735_ = lean_ctor_get(v_l_614_, 1);
v_v_736_ = lean_ctor_get(v_l_614_, 2);
v_isSharedCheck_747_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_748_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_750_);
v___x_738_ = v_l_614_;
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_v_736_);
lean_inc(v_k_735_);
lean_dec(v_l_614_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(3u);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 3, v_r_716_);
lean_ctor_set(v___x_738_, 2, v_v_613_);
lean_ctor_set(v___x_738_, 1, v_k_612_);
lean_ctor_set(v___x_738_, 0, v___x_624_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_r_716_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_r_716_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_742_);
lean_ctor_set(v___x_617_, 3, v_l_715_);
lean_ctor_set(v___x_617_, 2, v_v_736_);
lean_ctor_set(v___x_617_, 1, v_k_735_);
lean_ctor_set(v___x_617_, 0, v___x_740_);
v___x_744_ = v___x_617_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_735_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_736_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_l_715_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
else
{
lean_object* v_r_751_; 
v_r_751_ = lean_ctor_get(v_l_614_, 4);
lean_inc(v_r_751_);
if (lean_obj_tag(v_r_751_) == 0)
{
lean_object* v_k_752_; lean_object* v_v_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_776_; 
lean_inc(v_l_715_);
v_k_752_ = lean_ctor_get(v_l_614_, 1);
v_v_753_ = lean_ctor_get(v_l_614_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_777_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_779_);
v___x_755_ = v_l_614_;
v_isShared_756_ = v_isSharedCheck_776_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_v_753_);
lean_inc(v_k_752_);
lean_dec(v_l_614_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_776_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_k_757_; lean_object* v_v_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_772_; 
v_k_757_ = lean_ctor_get(v_r_751_, 1);
v_v_758_ = lean_ctor_get(v_r_751_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v_r_751_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_773_ = lean_ctor_get(v_r_751_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_751_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_751_, 0);
lean_dec(v_unused_775_);
v___x_760_ = v_r_751_;
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_v_758_);
lean_inc(v_k_757_);
lean_dec(v_r_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(3u);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_l_715_);
lean_ctor_set(v___x_760_, 3, v_l_715_);
lean_ctor_set(v___x_760_, 2, v_v_753_);
lean_ctor_set(v___x_760_, 1, v_k_752_);
lean_ctor_set(v___x_760_, 0, v___x_624_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_752_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_753_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_l_715_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_715_);
v___x_764_ = v_reuseFailAlloc_771_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 4, v_l_715_);
lean_ctor_set(v___x_755_, 2, v_v_613_);
lean_ctor_set(v___x_755_, 1, v_k_612_);
lean_ctor_set(v___x_755_, 0, v___x_624_);
v___x_766_ = v___x_755_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_l_715_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_l_715_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_766_);
lean_ctor_set(v___x_617_, 3, v___x_764_);
lean_ctor_set(v___x_617_, 2, v_v_758_);
lean_ctor_set(v___x_617_, 1, v_k_757_);
lean_ctor_set(v___x_617_, 0, v___x_762_);
v___x_768_ = v___x_617_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_unsigned_to_nat(2u);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_r_751_);
lean_ctor_set(v___x_617_, 0, v___x_780_);
v___x_782_ = v___x_617_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_l_614_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_r_751_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_785_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_l_614_);
lean_ctor_set(v___x_617_, 0, v___x_624_);
v___x_785_ = v___x_617_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_l_614_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_l_614_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_del_object(v___x_617_);
lean_dec(v_v_613_);
lean_dec(v_k_612_);
if (lean_obj_tag(v_l_614_) == 0)
{
if (lean_obj_tag(v_r_615_) == 0)
{
lean_object* v_size_787_; lean_object* v_k_788_; lean_object* v_v_789_; lean_object* v_l_790_; lean_object* v_r_791_; lean_object* v_size_792_; lean_object* v_k_793_; lean_object* v_v_794_; lean_object* v_l_795_; lean_object* v_r_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_size_787_ = lean_ctor_get(v_l_614_, 0);
v_k_788_ = lean_ctor_get(v_l_614_, 1);
v_v_789_ = lean_ctor_get(v_l_614_, 2);
v_l_790_ = lean_ctor_get(v_l_614_, 3);
v_r_791_ = lean_ctor_get(v_l_614_, 4);
lean_inc(v_r_791_);
v_size_792_ = lean_ctor_get(v_r_615_, 0);
v_k_793_ = lean_ctor_get(v_r_615_, 1);
v_v_794_ = lean_ctor_get(v_r_615_, 2);
v_l_795_ = lean_ctor_get(v_r_615_, 3);
lean_inc(v_l_795_);
v_r_796_ = lean_ctor_get(v_r_615_, 4);
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_dec_lt(v_size_787_, v_size_792_);
if (v___x_798_ == 0)
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_934_; 
lean_inc(v_l_790_);
lean_inc(v_v_789_);
lean_inc(v_k_788_);
v_isSharedCheck_934_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_935_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_l_614_, 2);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_614_, 1);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_939_);
v___x_800_ = v_l_614_;
v_isShared_801_ = v_isSharedCheck_934_;
goto v_resetjp_799_;
}
else
{
lean_dec(v_l_614_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_934_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v_tree_803_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_788_, v_v_789_, v_l_790_, v_r_791_);
v_tree_803_ = lean_ctor_get(v___x_802_, 2);
lean_inc(v_tree_803_);
if (lean_obj_tag(v_tree_803_) == 0)
{
lean_object* v_k_804_; lean_object* v_v_805_; lean_object* v_size_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_k_804_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_804_);
v_v_805_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_805_);
lean_dec_ref(v___x_802_);
v_size_806_ = lean_ctor_get(v_tree_803_, 0);
v___x_807_ = lean_unsigned_to_nat(3u);
v___x_808_ = lean_nat_mul(v___x_807_, v_size_806_);
v___x_809_ = lean_nat_dec_lt(v___x_808_, v_size_792_);
lean_dec(v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_dec(v_l_795_);
v___x_810_ = lean_nat_add(v___x_797_, v_size_806_);
v___x_811_ = lean_nat_add(v___x_810_, v_size_792_);
lean_dec(v___x_810_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_r_615_);
lean_ctor_set(v___x_800_, 3, v_tree_803_);
lean_ctor_set(v___x_800_, 2, v_v_805_);
lean_ctor_set(v___x_800_, 1, v_k_804_);
lean_ctor_set(v___x_800_, 0, v___x_811_);
v___x_813_ = v___x_800_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_tree_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_r_615_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_869_; 
lean_inc(v_r_796_);
lean_inc(v_v_794_);
lean_inc(v_k_793_);
lean_inc(v_size_792_);
v_isSharedCheck_869_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_870_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_r_615_, 2);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_r_615_, 1);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_874_);
v___x_816_ = v_r_615_;
v_isShared_817_ = v_isSharedCheck_869_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_r_615_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_869_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_size_818_; lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_l_821_; lean_object* v_r_822_; lean_object* v_size_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_size_818_ = lean_ctor_get(v_l_795_, 0);
v_k_819_ = lean_ctor_get(v_l_795_, 1);
v_v_820_ = lean_ctor_get(v_l_795_, 2);
v_l_821_ = lean_ctor_get(v_l_795_, 3);
v_r_822_ = lean_ctor_get(v_l_795_, 4);
v_size_823_ = lean_ctor_get(v_r_796_, 0);
v___x_824_ = lean_unsigned_to_nat(2u);
v___x_825_ = lean_nat_mul(v___x_824_, v_size_823_);
v___x_826_ = lean_nat_dec_lt(v_size_818_, v___x_825_);
lean_dec(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_r_822_);
lean_inc(v_l_821_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_l_795_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_855_ = lean_ctor_get(v_l_795_, 4);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_l_795_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_l_795_, 2);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_l_795_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_l_795_, 0);
lean_dec(v_unused_859_);
v___x_828_ = v_l_795_;
v_isShared_829_ = v_isSharedCheck_854_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_l_795_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_854_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_844_; 
v___x_830_ = lean_nat_add(v___x_797_, v_size_806_);
v___x_831_ = lean_nat_add(v___x_830_, v_size_792_);
lean_dec(v_size_792_);
if (lean_obj_tag(v_l_821_) == 0)
{
lean_object* v_size_852_; 
v_size_852_ = lean_ctor_get(v_l_821_, 0);
lean_inc(v_size_852_);
v___y_844_ = v_size_852_;
goto v___jp_843_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___y_844_ = v___x_853_;
goto v___jp_843_;
}
v___jp_832_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_nat_add(v___y_833_, v___y_835_);
lean_dec(v___y_835_);
lean_dec(v___y_833_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v_r_796_);
lean_ctor_set(v___x_828_, 3, v_r_822_);
lean_ctor_set(v___x_828_, 2, v_v_794_);
lean_ctor_set(v___x_828_, 1, v_k_793_);
lean_ctor_set(v___x_828_, 0, v___x_836_);
v___x_838_ = v___x_828_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_r_796_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 4, v___x_838_);
lean_ctor_set(v___x_816_, 3, v___y_834_);
lean_ctor_set(v___x_816_, 2, v_v_820_);
lean_ctor_set(v___x_816_, 1, v_k_819_);
lean_ctor_set(v___x_816_, 0, v___x_831_);
v___x_840_ = v___x_816_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v___y_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_nat_add(v___x_830_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___x_830_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_l_821_);
lean_ctor_set(v___x_800_, 3, v_tree_803_);
lean_ctor_set(v___x_800_, 2, v_v_805_);
lean_ctor_set(v___x_800_, 1, v_k_804_);
lean_ctor_set(v___x_800_, 0, v___x_845_);
v___x_847_ = v___x_800_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_tree_803_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_l_821_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_nat_add(v___x_797_, v_size_823_);
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_size_849_; 
v_size_849_ = lean_ctor_get(v_r_822_, 0);
lean_inc(v_size_849_);
v___y_833_ = v___x_848_;
v___y_834_ = v___x_847_;
v___y_835_ = v_size_849_;
goto v___jp_832_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___y_833_ = v___x_848_;
v___y_834_ = v___x_847_;
v___y_835_ = v___x_850_;
goto v___jp_832_;
}
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_860_ = lean_nat_add(v___x_797_, v_size_806_);
v___x_861_ = lean_nat_add(v___x_860_, v_size_792_);
lean_dec(v_size_792_);
v___x_862_ = lean_nat_add(v___x_860_, v_size_818_);
lean_dec(v___x_860_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 4, v_l_795_);
lean_ctor_set(v___x_816_, 3, v_tree_803_);
lean_ctor_set(v___x_816_, 2, v_v_805_);
lean_ctor_set(v___x_816_, 1, v_k_804_);
lean_ctor_set(v___x_816_, 0, v___x_862_);
v___x_864_ = v___x_816_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_tree_803_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_l_795_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_r_796_);
lean_ctor_set(v___x_800_, 3, v___x_864_);
lean_ctor_set(v___x_800_, 2, v_v_794_);
lean_ctor_set(v___x_800_, 1, v_k_793_);
lean_ctor_set(v___x_800_, 0, v___x_861_);
v___x_866_ = v___x_800_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_r_796_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
else
{
lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_928_; 
lean_inc(v_r_796_);
lean_inc(v_v_794_);
lean_inc(v_k_793_);
lean_inc(v_size_792_);
v_isSharedCheck_928_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; 
v_unused_929_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_r_615_, 2);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_r_615_, 1);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_933_);
v___x_876_ = v_r_615_;
v_isShared_877_ = v_isSharedCheck_928_;
goto v_resetjp_875_;
}
else
{
lean_dec(v_r_615_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_928_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
if (lean_obj_tag(v_l_795_) == 0)
{
if (lean_obj_tag(v_r_796_) == 0)
{
lean_object* v_k_878_; lean_object* v_v_879_; lean_object* v_size_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v_k_878_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_878_);
v_v_879_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_879_);
lean_dec_ref(v___x_802_);
v_size_880_ = lean_ctor_get(v_l_795_, 0);
v___x_881_ = lean_nat_add(v___x_797_, v_size_792_);
lean_dec(v_size_792_);
v___x_882_ = lean_nat_add(v___x_797_, v_size_880_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 4, v_l_795_);
lean_ctor_set(v___x_876_, 3, v_tree_803_);
lean_ctor_set(v___x_876_, 2, v_v_879_);
lean_ctor_set(v___x_876_, 1, v_k_878_);
lean_ctor_set(v___x_876_, 0, v___x_882_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_tree_803_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_l_795_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_r_796_);
lean_ctor_set(v___x_800_, 3, v___x_884_);
lean_ctor_set(v___x_800_, 2, v_v_794_);
lean_ctor_set(v___x_800_, 1, v_k_793_);
lean_ctor_set(v___x_800_, 0, v___x_881_);
v___x_886_ = v___x_800_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_r_796_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_k_889_; lean_object* v_v_890_; lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_size_792_);
v_k_889_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_889_);
v_v_890_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_890_);
lean_dec_ref(v___x_802_);
v_k_891_ = lean_ctor_get(v_l_795_, 1);
v_v_892_ = lean_ctor_get(v_l_795_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_l_795_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_907_ = lean_ctor_get(v_l_795_, 4);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_l_795_, 3);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_l_795_, 0);
lean_dec(v_unused_909_);
v___x_894_ = v_l_795_;
v_isShared_895_ = v_isSharedCheck_906_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_v_892_);
lean_inc(v_k_891_);
lean_dec(v_l_795_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_906_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(3u);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v_r_796_);
lean_ctor_set(v___x_894_, 3, v_r_796_);
lean_ctor_set(v___x_894_, 2, v_v_890_);
lean_ctor_set(v___x_894_, 1, v_k_889_);
lean_ctor_set(v___x_894_, 0, v___x_797_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_889_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_r_796_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_796_);
v___x_898_ = v_reuseFailAlloc_905_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 3, v_r_796_);
lean_ctor_set(v___x_876_, 0, v___x_797_);
v___x_900_ = v___x_876_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_r_796_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_796_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___x_900_);
lean_ctor_set(v___x_800_, 3, v___x_898_);
lean_ctor_set(v___x_800_, 2, v_v_892_);
lean_ctor_set(v___x_800_, 1, v_k_891_);
lean_ctor_set(v___x_800_, 0, v___x_896_);
v___x_902_ = v___x_800_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_892_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v___x_900_);
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
else
{
if (lean_obj_tag(v_r_796_) == 0)
{
lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v_size_792_);
v_k_910_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_910_);
v_v_911_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_911_);
lean_dec_ref(v___x_802_);
v___x_912_ = lean_unsigned_to_nat(3u);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 4, v_l_795_);
lean_ctor_set(v___x_876_, 2, v_v_911_);
lean_ctor_set(v___x_876_, 1, v_k_910_);
lean_ctor_set(v___x_876_, 0, v___x_797_);
v___x_914_ = v___x_876_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_l_795_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_l_795_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_r_796_);
lean_ctor_set(v___x_800_, 3, v___x_914_);
lean_ctor_set(v___x_800_, 2, v_v_794_);
lean_ctor_set(v___x_800_, 1, v_k_793_);
lean_ctor_set(v___x_800_, 0, v___x_912_);
v___x_916_ = v___x_800_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_r_796_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v___x_922_; 
v_k_919_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_919_);
v_v_920_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_920_);
lean_dec_ref(v___x_802_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 3, v_r_796_);
v___x_922_ = v___x_876_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_size_792_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_r_796_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_r_796_);
v___x_922_ = v_reuseFailAlloc_927_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_unsigned_to_nat(2u);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___x_922_);
lean_ctor_set(v___x_800_, 3, v_r_796_);
lean_ctor_set(v___x_800_, 2, v_v_920_);
lean_ctor_set(v___x_800_, 1, v_k_919_);
lean_ctor_set(v___x_800_, 0, v___x_923_);
v___x_925_ = v___x_800_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_r_796_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v___x_922_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
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
lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1092_; 
lean_inc(v_r_796_);
lean_inc(v_v_794_);
lean_inc(v_k_793_);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1093_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_r_615_, 2);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_r_615_, 1);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_1097_);
v___x_941_ = v_r_615_;
v_isShared_942_ = v_isSharedCheck_1092_;
goto v_resetjp_940_;
}
else
{
lean_dec(v_r_615_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1092_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v_tree_944_; 
v___x_943_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_793_, v_v_794_, v_l_795_, v_r_796_);
v_tree_944_ = lean_ctor_get(v___x_943_, 2);
lean_inc(v_tree_944_);
if (lean_obj_tag(v_tree_944_) == 0)
{
lean_object* v_k_945_; lean_object* v_v_946_; lean_object* v_size_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_k_945_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_k_945_);
v_v_946_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_v_946_);
lean_dec_ref(v___x_943_);
v_size_947_ = lean_ctor_get(v_tree_944_, 0);
v___x_948_ = lean_unsigned_to_nat(3u);
v___x_949_ = lean_nat_mul(v___x_948_, v_size_947_);
v___x_950_ = lean_nat_dec_lt(v___x_949_, v_size_787_);
lean_dec(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec(v_r_791_);
v___x_951_ = lean_nat_add(v___x_797_, v_size_787_);
v___x_952_ = lean_nat_add(v___x_951_, v_size_947_);
lean_dec(v___x_951_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_tree_944_);
lean_ctor_set(v___x_941_, 3, v_l_614_);
lean_ctor_set(v___x_941_, 2, v_v_946_);
lean_ctor_set(v___x_941_, 1, v_k_945_);
lean_ctor_set(v___x_941_, 0, v___x_952_);
v___x_954_ = v___x_941_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_l_614_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_tree_944_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1021_; 
lean_inc(v_l_790_);
lean_inc(v_v_789_);
lean_inc(v_k_788_);
lean_inc(v_size_787_);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1022_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_614_, 2);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_l_614_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_1026_);
v___x_957_ = v_l_614_;
v_isShared_958_ = v_isSharedCheck_1021_;
goto v_resetjp_956_;
}
else
{
lean_dec(v_l_614_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1021_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_size_959_; lean_object* v_size_960_; lean_object* v_k_961_; lean_object* v_v_962_; lean_object* v_l_963_; lean_object* v_r_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_size_959_ = lean_ctor_get(v_l_790_, 0);
v_size_960_ = lean_ctor_get(v_r_791_, 0);
v_k_961_ = lean_ctor_get(v_r_791_, 1);
v_v_962_ = lean_ctor_get(v_r_791_, 2);
v_l_963_ = lean_ctor_get(v_r_791_, 3);
v_r_964_ = lean_ctor_get(v_r_791_, 4);
v___x_965_ = lean_unsigned_to_nat(2u);
v___x_966_ = lean_nat_mul(v___x_965_, v_size_959_);
v___x_967_ = lean_nat_dec_lt(v_size_960_, v___x_966_);
lean_dec(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1005_; 
lean_inc(v_r_964_);
lean_inc(v_l_963_);
lean_inc(v_v_962_);
lean_inc(v_k_961_);
lean_del_object(v___x_957_);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_r_791_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; lean_object* v_unused_1010_; 
v_unused_1006_ = lean_ctor_get(v_r_791_, 4);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_r_791_, 3);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_r_791_, 2);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_r_791_, 1);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_r_791_, 0);
lean_dec(v_unused_1010_);
v___x_969_ = v_r_791_;
v_isShared_970_ = v_isSharedCheck_1005_;
goto v_resetjp_968_;
}
else
{
lean_dec(v_r_791_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1005_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___x_993_; lean_object* v___y_995_; 
v___x_971_ = lean_nat_add(v___x_797_, v_size_787_);
lean_dec(v_size_787_);
v___x_972_ = lean_nat_add(v___x_971_, v_size_947_);
lean_dec(v___x_971_);
v___x_993_ = lean_nat_add(v___x_797_, v_size_959_);
if (lean_obj_tag(v_l_963_) == 0)
{
lean_object* v_size_1003_; 
v_size_1003_ = lean_ctor_get(v_l_963_, 0);
lean_inc(v_size_1003_);
v___y_995_ = v_size_1003_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___y_995_ = v___x_1004_;
goto v___jp_994_;
}
v___jp_973_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_nat_add(v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_inc_ref(v_tree_944_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v_tree_944_);
lean_ctor_set(v___x_969_, 3, v_r_964_);
lean_ctor_set(v___x_969_, 2, v_v_946_);
lean_ctor_set(v___x_969_, 1, v_k_945_);
lean_ctor_set(v___x_969_, 0, v___x_977_);
v___x_979_ = v___x_969_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_r_964_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_tree_944_);
v___x_979_ = v_reuseFailAlloc_992_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_isSharedCheck_986_ = !lean_is_exclusive(v_tree_944_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; 
v_unused_987_ = lean_ctor_get(v_tree_944_, 4);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_tree_944_, 3);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_tree_944_, 2);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_tree_944_, 1);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_tree_944_, 0);
lean_dec(v_unused_991_);
v___x_981_ = v_tree_944_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_dec(v_tree_944_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 4, v___x_979_);
lean_ctor_set(v___x_981_, 3, v___y_974_);
lean_ctor_set(v___x_981_, 2, v_v_962_);
lean_ctor_set(v___x_981_, 1, v_k_961_);
lean_ctor_set(v___x_981_, 0, v___x_972_);
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_k_961_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_v_962_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v___y_974_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___x_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = lean_nat_add(v___x_993_, v___y_995_);
lean_dec(v___y_995_);
lean_dec(v___x_993_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_l_963_);
lean_ctor_set(v___x_941_, 3, v_l_790_);
lean_ctor_set(v___x_941_, 2, v_v_789_);
lean_ctor_set(v___x_941_, 1, v_k_788_);
lean_ctor_set(v___x_941_, 0, v___x_996_);
v___x_998_ = v___x_941_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_l_790_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_l_963_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; 
v___x_999_ = lean_nat_add(v___x_797_, v_size_947_);
if (lean_obj_tag(v_r_964_) == 0)
{
lean_object* v_size_1000_; 
v_size_1000_ = lean_ctor_get(v_r_964_, 0);
lean_inc(v_size_1000_);
v___y_974_ = v___x_998_;
v___y_975_ = v___x_999_;
v___y_976_ = v_size_1000_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v___y_974_ = v___x_998_;
v___y_975_ = v___x_999_;
v___y_976_ = v___x_1001_;
goto v___jp_973_;
}
}
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1011_ = lean_nat_add(v___x_797_, v_size_787_);
lean_dec(v_size_787_);
v___x_1012_ = lean_nat_add(v___x_1011_, v_size_947_);
lean_dec(v___x_1011_);
v___x_1013_ = lean_nat_add(v___x_797_, v_size_947_);
v___x_1014_ = lean_nat_add(v___x_1013_, v_size_960_);
lean_dec(v___x_1013_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_tree_944_);
lean_ctor_set(v___x_941_, 3, v_r_791_);
lean_ctor_set(v___x_941_, 2, v_v_946_);
lean_ctor_set(v___x_941_, 1, v_k_945_);
lean_ctor_set(v___x_941_, 0, v___x_1014_);
v___x_1016_ = v___x_941_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_r_791_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_tree_944_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 4, v___x_1016_);
lean_ctor_set(v___x_957_, 0, v___x_1012_);
v___x_1018_ = v___x_957_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_l_790_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_790_) == 0)
{
lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1050_; 
lean_inc_ref(v_l_790_);
lean_inc(v_v_789_);
lean_inc(v_k_788_);
lean_inc(v_size_787_);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1051_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_l_614_, 2);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_l_614_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_1055_);
v___x_1028_ = v_l_614_;
v_isShared_1029_ = v_isSharedCheck_1050_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v_l_614_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1050_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
if (lean_obj_tag(v_r_791_) == 0)
{
lean_object* v_k_1030_; lean_object* v_v_1031_; lean_object* v_size_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v_k_1030_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_k_1030_);
v_v_1031_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_v_1031_);
lean_dec_ref(v___x_943_);
v_size_1032_ = lean_ctor_get(v_r_791_, 0);
v___x_1033_ = lean_nat_add(v___x_797_, v_size_787_);
lean_dec(v_size_787_);
v___x_1034_ = lean_nat_add(v___x_797_, v_size_1032_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_tree_944_);
lean_ctor_set(v___x_941_, 3, v_r_791_);
lean_ctor_set(v___x_941_, 2, v_v_1031_);
lean_ctor_set(v___x_941_, 1, v_k_1030_);
lean_ctor_set(v___x_941_, 0, v___x_1034_);
v___x_1036_ = v___x_941_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_1030_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_1031_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_r_791_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_tree_944_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 4, v___x_1036_);
lean_ctor_set(v___x_1028_, 0, v___x_1033_);
v___x_1038_ = v___x_1028_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_l_790_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_object* v_k_1041_; lean_object* v_v_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec(v_size_787_);
v_k_1041_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_k_1041_);
v_v_1042_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_v_1042_);
lean_dec_ref(v___x_943_);
v___x_1043_ = lean_unsigned_to_nat(3u);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_r_791_);
lean_ctor_set(v___x_941_, 3, v_r_791_);
lean_ctor_set(v___x_941_, 2, v_v_1042_);
lean_ctor_set(v___x_941_, 1, v_k_1041_);
lean_ctor_set(v___x_941_, 0, v___x_797_);
v___x_1045_ = v___x_941_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_1041_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_r_791_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_r_791_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 4, v___x_1045_);
lean_ctor_set(v___x_1028_, 0, v___x_1043_);
v___x_1047_ = v___x_1028_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_l_790_);
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
}
}
else
{
if (lean_obj_tag(v_r_791_) == 0)
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1080_; 
lean_inc(v_l_790_);
lean_inc(v_v_789_);
lean_inc(v_k_788_);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_l_614_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; 
v_unused_1081_ = lean_ctor_get(v_l_614_, 4);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_l_614_, 3);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_614_, 2);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_614_, 1);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_l_614_, 0);
lean_dec(v_unused_1085_);
v___x_1057_ = v_l_614_;
v_isShared_1058_ = v_isSharedCheck_1080_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v_l_614_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1080_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_k_1059_; lean_object* v_v_1060_; lean_object* v_k_1061_; lean_object* v_v_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1076_; 
v_k_1059_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_k_1059_);
v_v_1060_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_v_1060_);
lean_dec_ref(v___x_943_);
v_k_1061_ = lean_ctor_get(v_r_791_, 1);
v_v_1062_ = lean_ctor_get(v_r_791_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_r_791_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1077_ = lean_ctor_get(v_r_791_, 4);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_r_791_, 3);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_r_791_, 0);
lean_dec(v_unused_1079_);
v___x_1064_ = v_r_791_;
v_isShared_1065_ = v_isSharedCheck_1076_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_v_1062_);
lean_inc(v_k_1061_);
lean_dec(v_r_791_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1076_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_unsigned_to_nat(3u);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 4, v_l_790_);
lean_ctor_set(v___x_1064_, 3, v_l_790_);
lean_ctor_set(v___x_1064_, 2, v_v_789_);
lean_ctor_set(v___x_1064_, 1, v_k_788_);
lean_ctor_set(v___x_1064_, 0, v___x_797_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_l_790_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_l_790_);
v___x_1068_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_l_790_);
lean_ctor_set(v___x_941_, 3, v_l_790_);
lean_ctor_set(v___x_941_, 2, v_v_1060_);
lean_ctor_set(v___x_941_, 1, v_k_1059_);
lean_ctor_set(v___x_941_, 0, v___x_797_);
v___x_1070_ = v___x_941_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_1060_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_l_790_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_l_790_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 4, v___x_1070_);
lean_ctor_set(v___x_1057_, 3, v___x_1068_);
lean_ctor_set(v___x_1057_, 2, v_v_1062_);
lean_ctor_set(v___x_1057_, 1, v_k_1061_);
lean_ctor_set(v___x_1057_, 0, v___x_1066_);
v___x_1072_ = v___x_1057_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1061_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1062_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
else
{
lean_object* v_k_1086_; lean_object* v_v_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v_k_1086_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_k_1086_);
v_v_1087_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_v_1087_);
lean_dec_ref(v___x_943_);
v___x_1088_ = lean_unsigned_to_nat(2u);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_r_791_);
lean_ctor_set(v___x_941_, 3, v_l_614_);
lean_ctor_set(v___x_941_, 2, v_v_1087_);
lean_ctor_set(v___x_941_, 1, v_k_1086_);
lean_ctor_set(v___x_941_, 0, v___x_1088_);
v___x_1090_ = v___x_941_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_l_614_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_r_791_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
}
else
{
return v_l_614_;
}
}
else
{
return v_r_615_;
}
}
}
else
{
lean_object* v_impl_1098_; lean_object* v___x_1099_; 
v_impl_1098_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_610_, v_l_614_);
v___x_1099_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1098_) == 0)
{
if (lean_obj_tag(v_r_615_) == 0)
{
lean_object* v_size_1100_; lean_object* v_size_1101_; lean_object* v_k_1102_; lean_object* v_v_1103_; lean_object* v_l_1104_; lean_object* v_r_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_size_1100_ = lean_ctor_get(v_impl_1098_, 0);
lean_inc(v_size_1100_);
v_size_1101_ = lean_ctor_get(v_r_615_, 0);
v_k_1102_ = lean_ctor_get(v_r_615_, 1);
v_v_1103_ = lean_ctor_get(v_r_615_, 2);
v_l_1104_ = lean_ctor_get(v_r_615_, 3);
lean_inc(v_l_1104_);
v_r_1105_ = lean_ctor_get(v_r_615_, 4);
v___x_1106_ = lean_unsigned_to_nat(3u);
v___x_1107_ = lean_nat_mul(v___x_1106_, v_size_1100_);
v___x_1108_ = lean_nat_dec_lt(v___x_1107_, v_size_1101_);
lean_dec(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_dec(v_l_1104_);
v___x_1109_ = lean_nat_add(v___x_1099_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1110_ = lean_nat_add(v___x_1109_, v_size_1101_);
lean_dec(v___x_1109_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 3, v_impl_1098_);
lean_ctor_set(v___x_617_, 0, v___x_1110_);
v___x_1112_ = v___x_617_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_impl_1098_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_r_615_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1177_; 
lean_inc(v_r_1105_);
lean_inc(v_v_1103_);
lean_inc(v_k_1102_);
lean_inc(v_size_1101_);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; 
v_unused_1178_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_r_615_, 2);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_r_615_, 1);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_1182_);
v___x_1115_ = v_r_615_;
v_isShared_1116_ = v_isSharedCheck_1177_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v_r_615_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1177_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_size_1117_; lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v_l_1120_; lean_object* v_r_1121_; lean_object* v_size_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_size_1117_ = lean_ctor_get(v_l_1104_, 0);
v_k_1118_ = lean_ctor_get(v_l_1104_, 1);
v_v_1119_ = lean_ctor_get(v_l_1104_, 2);
v_l_1120_ = lean_ctor_get(v_l_1104_, 3);
v_r_1121_ = lean_ctor_get(v_l_1104_, 4);
v_size_1122_ = lean_ctor_get(v_r_1105_, 0);
v___x_1123_ = lean_unsigned_to_nat(2u);
v___x_1124_ = lean_nat_mul(v___x_1123_, v_size_1122_);
v___x_1125_ = lean_nat_dec_lt(v_size_1117_, v___x_1124_);
lean_dec(v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1153_; 
lean_inc(v_r_1121_);
lean_inc(v_l_1120_);
lean_inc(v_v_1119_);
lean_inc(v_k_1118_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_l_1104_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1154_ = lean_ctor_get(v_l_1104_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_l_1104_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_l_1104_, 2);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_l_1104_, 1);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_l_1104_, 0);
lean_dec(v_unused_1158_);
v___x_1127_ = v_l_1104_;
v_isShared_1128_ = v_isSharedCheck_1153_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_l_1104_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1153_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1143_; 
v___x_1129_ = lean_nat_add(v___x_1099_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1130_ = lean_nat_add(v___x_1129_, v_size_1101_);
lean_dec(v_size_1101_);
if (lean_obj_tag(v_l_1120_) == 0)
{
lean_object* v_size_1151_; 
v_size_1151_ = lean_ctor_get(v_l_1120_, 0);
lean_inc(v_size_1151_);
v___y_1143_ = v_size_1151_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v___y_1143_ = v___x_1152_;
goto v___jp_1142_;
}
v___jp_1131_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_nat_add(v___y_1132_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec(v___y_1132_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v_r_1105_);
lean_ctor_set(v___x_1127_, 3, v_r_1121_);
lean_ctor_set(v___x_1127_, 2, v_v_1103_);
lean_ctor_set(v___x_1127_, 1, v_k_1102_);
lean_ctor_set(v___x_1127_, 0, v___x_1135_);
v___x_1137_ = v___x_1127_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_1102_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_1103_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_r_1105_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 4, v___x_1137_);
lean_ctor_set(v___x_1115_, 3, v___y_1133_);
lean_ctor_set(v___x_1115_, 2, v_v_1119_);
lean_ctor_set(v___x_1115_, 1, v_k_1118_);
lean_ctor_set(v___x_1115_, 0, v___x_1130_);
v___x_1139_ = v___x_1115_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1118_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1119_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v___y_1133_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
v___jp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_nat_add(v___x_1129_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec(v___x_1129_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_l_1120_);
lean_ctor_set(v___x_617_, 3, v_impl_1098_);
lean_ctor_set(v___x_617_, 0, v___x_1144_);
v___x_1146_ = v___x_617_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_impl_1098_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_l_1120_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_nat_add(v___x_1099_, v_size_1122_);
if (lean_obj_tag(v_r_1121_) == 0)
{
lean_object* v_size_1148_; 
v_size_1148_ = lean_ctor_get(v_r_1121_, 0);
lean_inc(v_size_1148_);
v___y_1132_ = v___x_1147_;
v___y_1133_ = v___x_1146_;
v___y_1134_ = v_size_1148_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___y_1132_ = v___x_1147_;
v___y_1133_ = v___x_1146_;
v___y_1134_ = v___x_1149_;
goto v___jp_1131_;
}
}
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_del_object(v___x_617_);
v___x_1159_ = lean_nat_add(v___x_1099_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1160_ = lean_nat_add(v___x_1159_, v_size_1101_);
lean_dec(v_size_1101_);
v___x_1161_ = lean_nat_add(v___x_1159_, v_size_1117_);
lean_dec(v___x_1159_);
lean_inc_ref(v_impl_1098_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 4, v_l_1104_);
lean_ctor_set(v___x_1115_, 3, v_impl_1098_);
lean_ctor_set(v___x_1115_, 2, v_v_613_);
lean_ctor_set(v___x_1115_, 1, v_k_612_);
lean_ctor_set(v___x_1115_, 0, v___x_1161_);
v___x_1163_ = v___x_1115_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_impl_1098_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_l_1104_);
v___x_1163_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_isSharedCheck_1170_ = !lean_is_exclusive(v_impl_1098_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1171_ = lean_ctor_get(v_impl_1098_, 4);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_impl_1098_, 3);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_impl_1098_, 2);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_impl_1098_, 1);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1098_, 0);
lean_dec(v_unused_1175_);
v___x_1165_ = v_impl_1098_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_dec(v_impl_1098_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 4, v_r_1105_);
lean_ctor_set(v___x_1165_, 3, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v_v_1103_);
lean_ctor_set(v___x_1165_, 1, v_k_1102_);
lean_ctor_set(v___x_1165_, 0, v___x_1160_);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_k_1102_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_v_1103_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_r_1105_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v_size_1183_ = lean_ctor_get(v_impl_1098_, 0);
lean_inc(v_size_1183_);
v___x_1184_ = lean_nat_add(v___x_1099_, v_size_1183_);
lean_dec(v_size_1183_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 3, v_impl_1098_);
lean_ctor_set(v___x_617_, 0, v___x_1184_);
v___x_1186_ = v___x_617_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_impl_1098_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_r_615_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
if (lean_obj_tag(v_r_615_) == 0)
{
lean_object* v_l_1188_; 
v_l_1188_ = lean_ctor_get(v_r_615_, 3);
lean_inc(v_l_1188_);
if (lean_obj_tag(v_l_1188_) == 0)
{
lean_object* v_r_1189_; 
v_r_1189_ = lean_ctor_get(v_r_615_, 4);
lean_inc(v_r_1189_);
if (lean_obj_tag(v_r_1189_) == 0)
{
lean_object* v_size_1190_; lean_object* v_k_1191_; lean_object* v_v_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1205_; 
v_size_1190_ = lean_ctor_get(v_r_615_, 0);
v_k_1191_ = lean_ctor_get(v_r_615_, 1);
v_v_1192_ = lean_ctor_get(v_r_615_, 2);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1206_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_1207_);
v___x_1194_ = v_r_615_;
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_v_1192_);
lean_inc(v_k_1191_);
lean_inc(v_size_1190_);
lean_dec(v_r_615_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_size_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v_size_1196_ = lean_ctor_get(v_l_1188_, 0);
v___x_1197_ = lean_nat_add(v___x_1099_, v_size_1190_);
lean_dec(v_size_1190_);
v___x_1198_ = lean_nat_add(v___x_1099_, v_size_1196_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 4, v_l_1188_);
lean_ctor_set(v___x_1194_, 3, v_impl_1098_);
lean_ctor_set(v___x_1194_, 2, v_v_613_);
lean_ctor_set(v___x_1194_, 1, v_k_612_);
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_impl_1098_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_l_1188_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_r_1189_);
lean_ctor_set(v___x_617_, 3, v___x_1200_);
lean_ctor_set(v___x_617_, 2, v_v_1192_);
lean_ctor_set(v___x_617_, 1, v_k_1191_);
lean_ctor_set(v___x_617_, 0, v___x_1197_);
v___x_1202_ = v___x_617_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1192_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_r_1189_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_k_1208_; lean_object* v_v_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1232_; 
v_k_1208_ = lean_ctor_get(v_r_615_, 1);
v_v_1209_ = lean_ctor_get(v_r_615_, 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1233_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_1235_);
v___x_1211_ = v_r_615_;
v_isShared_1212_ = v_isSharedCheck_1232_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_v_1209_);
lean_inc(v_k_1208_);
lean_dec(v_r_615_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1232_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1228_; 
v_k_1213_ = lean_ctor_get(v_l_1188_, 1);
v_v_1214_ = lean_ctor_get(v_l_1188_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_l_1188_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; lean_object* v_unused_1230_; lean_object* v_unused_1231_; 
v_unused_1229_ = lean_ctor_get(v_l_1188_, 4);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_l_1188_, 3);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_l_1188_, 0);
lean_dec(v_unused_1231_);
v___x_1216_ = v_l_1188_;
v_isShared_1217_ = v_isSharedCheck_1228_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_v_1214_);
lean_inc(v_k_1213_);
lean_dec(v_l_1188_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1228_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_unsigned_to_nat(3u);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 4, v_r_1189_);
lean_ctor_set(v___x_1216_, 3, v_r_1189_);
lean_ctor_set(v___x_1216_, 2, v_v_613_);
lean_ctor_set(v___x_1216_, 1, v_k_612_);
lean_ctor_set(v___x_1216_, 0, v___x_1099_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_r_1189_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_r_1189_);
v___x_1220_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 3, v_r_1189_);
lean_ctor_set(v___x_1211_, 0, v___x_1099_);
v___x_1222_ = v___x_1211_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_r_1189_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_r_1189_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_1222_);
lean_ctor_set(v___x_617_, 3, v___x_1220_);
lean_ctor_set(v___x_617_, 2, v_v_1214_);
lean_ctor_set(v___x_617_, 1, v_k_1213_);
lean_ctor_set(v___x_617_, 0, v___x_1218_);
v___x_1224_ = v___x_617_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_1213_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_1214_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1236_; 
v_r_1236_ = lean_ctor_get(v_r_615_, 4);
lean_inc(v_r_1236_);
if (lean_obj_tag(v_r_1236_) == 0)
{
lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v_k_1237_ = lean_ctor_get(v_r_615_, 1);
v_v_1238_ = lean_ctor_get(v_r_615_, 2);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; lean_object* v_unused_1251_; lean_object* v_unused_1252_; 
v_unused_1250_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_1252_);
v___x_1240_ = v_r_615_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_v_1238_);
lean_inc(v_k_1237_);
lean_dec(v_r_615_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_unsigned_to_nat(3u);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 4, v_l_1188_);
lean_ctor_set(v___x_1240_, 2, v_v_613_);
lean_ctor_set(v___x_1240_, 1, v_k_612_);
lean_ctor_set(v___x_1240_, 0, v___x_1099_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_l_1188_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_l_1188_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_r_1236_);
lean_ctor_set(v___x_617_, 3, v___x_1244_);
lean_ctor_set(v___x_617_, 2, v_v_1238_);
lean_ctor_set(v___x_617_, 1, v_k_1237_);
lean_ctor_set(v___x_617_, 0, v___x_1242_);
v___x_1246_ = v___x_617_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_r_1236_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_size_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1266_; 
v_size_1253_ = lean_ctor_get(v_r_615_, 0);
v_k_1254_ = lean_ctor_get(v_r_615_, 1);
v_v_1255_ = lean_ctor_get(v_r_615_, 2);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; lean_object* v_unused_1268_; 
v_unused_1267_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_1267_);
v_unused_1268_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_1268_);
v___x_1257_ = v_r_615_;
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
lean_inc(v_size_1253_);
lean_dec(v_r_615_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v_r_1236_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_r_1236_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_r_1236_);
v___x_1260_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_unsigned_to_nat(2u);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_1260_);
lean_ctor_set(v___x_617_, 3, v_r_1236_);
lean_ctor_set(v___x_617_, 0, v___x_1261_);
v___x_1263_ = v___x_617_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_r_1236_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v___x_1260_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
else
{
lean_object* v___x_1270_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 3, v_r_615_);
lean_ctor_set(v___x_617_, 0, v___x_1099_);
v___x_1270_ = v___x_617_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_r_615_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_r_615_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
else
{
return v_t_611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg___boxed(lean_object* v_k_1274_, lean_object* v_t_1275_){
_start:
{
uint64_t v_k_boxed_1276_; lean_object* v_res_1277_; 
v_k_boxed_1276_ = lean_unbox_uint64(v_k_1274_);
lean_dec_ref(v_k_1274_);
v_res_1277_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_boxed_1276_, v_t_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(uint64_t v_h_1278_, lean_object* v_st_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_h_1278_, v_st_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(lean_object* v_h_1281_, lean_object* v_st_1282_){
_start:
{
uint64_t v_h_boxed_1283_; lean_object* v_res_1284_; 
v_h_boxed_1283_ = lean_unbox_uint64(v_h_1281_);
lean_dec_ref(v_h_1281_);
v_res_1284_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_1283_, v_st_1282_);
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
v___x_1291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set(v___x_1291_, 2, v___x_1290_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
lean_ctor_set(v___x_1291_, 4, v___x_1290_);
lean_ctor_set(v___x_1291_, 5, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(uint64_t v_h_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_env_1297_; lean_object* v_nextMacroScope_1298_; lean_object* v_ngen_1299_; lean_object* v_auxDeclNGen_1300_; lean_object* v_traceState_1301_; lean_object* v_messages_1302_; lean_object* v_infoState_1303_; lean_object* v_snapshotTasks_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1334_; 
v___x_1296_ = lean_st_ref_take(v___y_1294_);
v_env_1297_ = lean_ctor_get(v___x_1296_, 0);
v_nextMacroScope_1298_ = lean_ctor_get(v___x_1296_, 1);
v_ngen_1299_ = lean_ctor_get(v___x_1296_, 2);
v_auxDeclNGen_1300_ = lean_ctor_get(v___x_1296_, 3);
v_traceState_1301_ = lean_ctor_get(v___x_1296_, 4);
v_messages_1302_ = lean_ctor_get(v___x_1296_, 6);
v_infoState_1303_ = lean_ctor_get(v___x_1296_, 7);
v_snapshotTasks_1304_ = lean_ctor_get(v___x_1296_, 8);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1296_, 5);
lean_dec(v_unused_1335_);
v___x_1306_ = v___x_1296_;
v_isShared_1307_ = v_isSharedCheck_1334_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_snapshotTasks_1304_);
lean_inc(v_infoState_1303_);
lean_inc(v_messages_1302_);
lean_inc(v_traceState_1301_);
lean_inc(v_auxDeclNGen_1300_);
lean_inc(v_ngen_1299_);
lean_inc(v_nextMacroScope_1298_);
lean_inc(v_env_1297_);
lean_dec(v___x_1296_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1334_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1308_ = lean_box_uint64(v_h_1292_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1309_, 0, v___x_1308_);
v___x_1310_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1311_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1310_, v_env_1297_, v___f_1309_);
v___x_1312_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 5, v___x_1312_);
lean_ctor_set(v___x_1306_, 0, v___x_1311_);
v___x_1314_ = v___x_1306_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_nextMacroScope_1298_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_ngen_1299_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_auxDeclNGen_1300_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_traceState_1301_);
lean_ctor_set(v_reuseFailAlloc_1333_, 5, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1333_, 6, v_messages_1302_);
lean_ctor_set(v_reuseFailAlloc_1333_, 7, v_infoState_1303_);
lean_ctor_set(v_reuseFailAlloc_1333_, 8, v_snapshotTasks_1304_);
v___x_1314_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_mctx_1317_; lean_object* v_zetaDeltaFVarIds_1318_; lean_object* v_postponed_1319_; lean_object* v_diag_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1331_; 
v___x_1315_ = lean_st_ref_set(v___y_1294_, v___x_1314_);
v___x_1316_ = lean_st_ref_take(v___y_1293_);
v_mctx_1317_ = lean_ctor_get(v___x_1316_, 0);
v_zetaDeltaFVarIds_1318_ = lean_ctor_get(v___x_1316_, 2);
v_postponed_1319_ = lean_ctor_get(v___x_1316_, 3);
v_diag_1320_ = lean_ctor_get(v___x_1316_, 4);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1316_, 1);
lean_dec(v_unused_1332_);
v___x_1322_ = v___x_1316_;
v_isShared_1323_ = v_isSharedCheck_1331_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_diag_1320_);
lean_inc(v_postponed_1319_);
lean_inc(v_zetaDeltaFVarIds_1318_);
lean_inc(v_mctx_1317_);
lean_dec(v___x_1316_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1331_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_mctx_1317_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_zetaDeltaFVarIds_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_postponed_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_diag_1320_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_st_ref_set(v___y_1293_, v___x_1326_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(lean_object* v_h_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint64_t v_h_boxed_1340_; lean_object* v_res_1341_; 
v_h_boxed_1340_ = lean_unbox_uint64(v_h_1336_);
lean_dec_ref(v_h_1336_);
v_res_1341_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_1340_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(lean_object* v_t_1342_, uint64_t v_k_1343_, lean_object* v_fallback_1344_){
_start:
{
if (lean_obj_tag(v_t_1342_) == 0)
{
lean_object* v_k_1345_; lean_object* v_v_1346_; lean_object* v_l_1347_; lean_object* v_r_1348_; uint64_t v___x_1349_; uint8_t v___x_1350_; 
v_k_1345_ = lean_ctor_get(v_t_1342_, 1);
v_v_1346_ = lean_ctor_get(v_t_1342_, 2);
v_l_1347_ = lean_ctor_get(v_t_1342_, 3);
v_r_1348_ = lean_ctor_get(v_t_1342_, 4);
v___x_1349_ = lean_unbox_uint64(v_k_1345_);
v___x_1350_ = lean_uint64_dec_lt(v_k_1343_, v___x_1349_);
if (v___x_1350_ == 0)
{
uint64_t v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = lean_unbox_uint64(v_k_1345_);
v___x_1352_ = lean_uint64_dec_eq(v_k_1343_, v___x_1351_);
if (v___x_1352_ == 0)
{
v_t_1342_ = v_r_1348_;
goto _start;
}
else
{
lean_inc(v_v_1346_);
return v_v_1346_;
}
}
else
{
v_t_1342_ = v_l_1347_;
goto _start;
}
}
else
{
lean_inc(v_fallback_1344_);
return v_fallback_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(lean_object* v_t_1355_, lean_object* v_k_1356_, lean_object* v_fallback_1357_){
_start:
{
uint64_t v_k_boxed_1358_; lean_object* v_res_1359_; 
v_k_boxed_1358_ = lean_unbox_uint64(v_k_1356_);
lean_dec_ref(v_k_1356_);
v_res_1359_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_1355_, v_k_boxed_1358_, v_fallback_1357_);
lean_dec(v_fallback_1357_);
lean_dec(v_t_1355_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(uint64_t v_k_1360_, lean_object* v_v_1361_, lean_object* v_t_1362_){
_start:
{
if (lean_obj_tag(v_t_1362_) == 0)
{
lean_object* v_size_1363_; lean_object* v_k_1364_; lean_object* v_v_1365_; lean_object* v_l_1366_; lean_object* v_r_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1651_; 
v_size_1363_ = lean_ctor_get(v_t_1362_, 0);
v_k_1364_ = lean_ctor_get(v_t_1362_, 1);
v_v_1365_ = lean_ctor_get(v_t_1362_, 2);
v_l_1366_ = lean_ctor_get(v_t_1362_, 3);
v_r_1367_ = lean_ctor_get(v_t_1362_, 4);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_t_1362_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1369_ = v_t_1362_;
v_isShared_1370_ = v_isSharedCheck_1651_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_r_1367_);
lean_inc(v_l_1366_);
lean_inc(v_v_1365_);
lean_inc(v_k_1364_);
lean_inc(v_size_1363_);
lean_dec(v_t_1362_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1651_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint64_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = lean_unbox_uint64(v_k_1364_);
v___x_1372_ = lean_uint64_dec_lt(v_k_1360_, v___x_1371_);
if (v___x_1372_ == 0)
{
uint64_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_unbox_uint64(v_k_1364_);
v___x_1374_ = lean_uint64_dec_eq(v_k_1360_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v_impl_1375_; lean_object* v___x_1376_; 
lean_dec(v_size_1363_);
v_impl_1375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1360_, v_v_1361_, v_r_1367_);
v___x_1376_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1366_) == 0)
{
lean_object* v_size_1377_; lean_object* v_size_1378_; lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_l_1381_; lean_object* v_r_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_size_1377_ = lean_ctor_get(v_l_1366_, 0);
v_size_1378_ = lean_ctor_get(v_impl_1375_, 0);
lean_inc(v_size_1378_);
v_k_1379_ = lean_ctor_get(v_impl_1375_, 1);
lean_inc(v_k_1379_);
v_v_1380_ = lean_ctor_get(v_impl_1375_, 2);
lean_inc(v_v_1380_);
v_l_1381_ = lean_ctor_get(v_impl_1375_, 3);
lean_inc(v_l_1381_);
v_r_1382_ = lean_ctor_get(v_impl_1375_, 4);
lean_inc(v_r_1382_);
v___x_1383_ = lean_unsigned_to_nat(3u);
v___x_1384_ = lean_nat_mul(v___x_1383_, v_size_1377_);
v___x_1385_ = lean_nat_dec_lt(v___x_1384_, v_size_1378_);
lean_dec(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_r_1382_);
lean_dec(v_l_1381_);
lean_dec(v_v_1380_);
lean_dec(v_k_1379_);
v___x_1386_ = lean_nat_add(v___x_1376_, v_size_1377_);
v___x_1387_ = lean_nat_add(v___x_1386_, v_size_1378_);
lean_dec(v_size_1378_);
lean_dec(v___x_1386_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_impl_1375_);
lean_ctor_set(v___x_1369_, 0, v___x_1387_);
v___x_1389_ = v___x_1369_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_l_1366_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_impl_1375_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; 
v_unused_1455_ = lean_ctor_get(v_impl_1375_, 4);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_impl_1375_, 2);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_impl_1375_, 1);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1459_);
v___x_1392_ = v_impl_1375_;
v_isShared_1393_ = v_isSharedCheck_1454_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_impl_1375_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1454_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_size_1394_; lean_object* v_k_1395_; lean_object* v_v_1396_; lean_object* v_l_1397_; lean_object* v_r_1398_; lean_object* v_size_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1394_ = lean_ctor_get(v_l_1381_, 0);
v_k_1395_ = lean_ctor_get(v_l_1381_, 1);
v_v_1396_ = lean_ctor_get(v_l_1381_, 2);
v_l_1397_ = lean_ctor_get(v_l_1381_, 3);
v_r_1398_ = lean_ctor_get(v_l_1381_, 4);
v_size_1399_ = lean_ctor_get(v_r_1382_, 0);
v___x_1400_ = lean_unsigned_to_nat(2u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1399_);
v___x_1402_ = lean_nat_dec_lt(v_size_1394_, v___x_1401_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1430_; 
lean_inc(v_r_1398_);
lean_inc(v_l_1397_);
lean_inc(v_v_1396_);
lean_inc(v_k_1395_);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_l_1381_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; 
v_unused_1431_ = lean_ctor_get(v_l_1381_, 4);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_l_1381_, 3);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_l_1381_, 2);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_l_1381_, 1);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_l_1381_, 0);
lean_dec(v_unused_1435_);
v___x_1404_ = v_l_1381_;
v_isShared_1405_ = v_isSharedCheck_1430_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_l_1381_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1430_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1420_; 
v___x_1406_ = lean_nat_add(v___x_1376_, v_size_1377_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1378_);
lean_dec(v_size_1378_);
if (lean_obj_tag(v_l_1397_) == 0)
{
lean_object* v_size_1428_; 
v_size_1428_ = lean_ctor_get(v_l_1397_, 0);
lean_inc(v_size_1428_);
v___y_1420_ = v_size_1428_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___y_1420_ = v___x_1429_;
goto v___jp_1419_;
}
v___jp_1408_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_nat_add(v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___y_1410_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_r_1382_);
lean_ctor_set(v___x_1404_, 3, v_r_1398_);
lean_ctor_set(v___x_1404_, 2, v_v_1380_);
lean_ctor_set(v___x_1404_, 1, v_k_1379_);
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_r_1398_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_r_1382_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1414_);
lean_ctor_set(v___x_1392_, 3, v___y_1409_);
lean_ctor_set(v___x_1392_, 2, v_v_1396_);
lean_ctor_set(v___x_1392_, 1, v_k_1395_);
lean_ctor_set(v___x_1392_, 0, v___x_1407_);
v___x_1416_ = v___x_1392_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1395_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1396_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v___y_1409_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_nat_add(v___x_1406_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec(v___x_1406_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_l_1397_);
lean_ctor_set(v___x_1369_, 0, v___x_1421_);
v___x_1423_ = v___x_1369_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_l_1366_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_l_1397_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_nat_add(v___x_1376_, v_size_1399_);
if (lean_obj_tag(v_r_1398_) == 0)
{
lean_object* v_size_1425_; 
v_size_1425_ = lean_ctor_get(v_r_1398_, 0);
lean_inc(v_size_1425_);
v___y_1409_ = v___x_1423_;
v___y_1410_ = v___x_1424_;
v___y_1411_ = v_size_1425_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___y_1409_ = v___x_1423_;
v___y_1410_ = v___x_1424_;
v___y_1411_ = v___x_1426_;
goto v___jp_1408_;
}
}
}
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_del_object(v___x_1369_);
v___x_1436_ = lean_nat_add(v___x_1376_, v_size_1377_);
v___x_1437_ = lean_nat_add(v___x_1436_, v_size_1378_);
lean_dec(v_size_1378_);
v___x_1438_ = lean_nat_add(v___x_1436_, v_size_1394_);
lean_dec(v___x_1436_);
lean_inc_ref(v_l_1366_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1381_);
lean_ctor_set(v___x_1392_, 3, v_l_1366_);
lean_ctor_set(v___x_1392_, 2, v_v_1365_);
lean_ctor_set(v___x_1392_, 1, v_k_1364_);
lean_ctor_set(v___x_1392_, 0, v___x_1438_);
v___x_1440_ = v___x_1392_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_l_1366_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_l_1381_);
v___x_1440_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v_l_1366_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_l_1366_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1366_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_l_1366_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1366_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1366_, 0);
lean_dec(v_unused_1452_);
v___x_1442_ = v_l_1366_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v_l_1366_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v_r_1382_);
lean_ctor_set(v___x_1442_, 3, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v_v_1380_);
lean_ctor_set(v___x_1442_, 1, v_k_1379_);
lean_ctor_set(v___x_1442_, 0, v___x_1437_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_r_1382_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1460_; 
v_l_1460_ = lean_ctor_get(v_impl_1375_, 3);
lean_inc(v_l_1460_);
if (lean_obj_tag(v_l_1460_) == 0)
{
lean_object* v_r_1461_; lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1486_; 
v_r_1461_ = lean_ctor_get(v_impl_1375_, 4);
v_k_1462_ = lean_ctor_get(v_impl_1375_, 1);
v_v_1463_ = lean_ctor_get(v_impl_1375_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1487_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1488_);
v___x_1465_ = v_impl_1375_;
v_isShared_1466_ = v_isSharedCheck_1486_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_r_1461_);
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
lean_dec(v_impl_1375_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1486_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1482_; 
v_k_1467_ = lean_ctor_get(v_l_1460_, 1);
v_v_1468_ = lean_ctor_get(v_l_1460_, 2);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_l_1460_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1483_ = lean_ctor_get(v_l_1460_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1460_, 3);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_l_1460_, 0);
lean_dec(v_unused_1485_);
v___x_1470_ = v_l_1460_;
v_isShared_1471_ = v_isSharedCheck_1482_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
lean_dec(v_l_1460_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1482_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1461_, 2);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v_r_1461_);
lean_ctor_set(v___x_1470_, 3, v_r_1461_);
lean_ctor_set(v___x_1470_, 2, v_v_1365_);
lean_ctor_set(v___x_1470_, 1, v_k_1364_);
lean_ctor_set(v___x_1470_, 0, v___x_1376_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_r_1461_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_r_1461_);
v___x_1474_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
lean_inc(v_r_1461_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 3, v_r_1461_);
lean_ctor_set(v___x_1465_, 0, v___x_1376_);
v___x_1476_ = v___x_1465_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1462_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1463_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1461_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1461_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v___x_1476_);
lean_ctor_set(v___x_1369_, 3, v___x_1474_);
lean_ctor_set(v___x_1369_, 2, v_v_1468_);
lean_ctor_set(v___x_1369_, 1, v_k_1467_);
lean_ctor_set(v___x_1369_, 0, v___x_1472_);
v___x_1478_ = v___x_1369_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
else
{
lean_object* v_r_1489_; 
v_r_1489_ = lean_ctor_get(v_impl_1375_, 4);
lean_inc(v_r_1489_);
if (lean_obj_tag(v_r_1489_) == 0)
{
lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1502_; 
v_k_1490_ = lean_ctor_get(v_impl_1375_, 1);
v_v_1491_ = lean_ctor_get(v_impl_1375_, 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1503_ = lean_ctor_get(v_impl_1375_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1505_);
v___x_1493_ = v_impl_1375_;
v_isShared_1494_ = v_isSharedCheck_1502_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_v_1491_);
lean_inc(v_k_1490_);
lean_dec(v_impl_1375_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1502_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unsigned_to_nat(3u);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_l_1460_);
lean_ctor_set(v___x_1493_, 2, v_v_1365_);
lean_ctor_set(v___x_1493_, 1, v_k_1364_);
lean_ctor_set(v___x_1493_, 0, v___x_1376_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1460_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_l_1460_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_r_1489_);
lean_ctor_set(v___x_1369_, 3, v___x_1497_);
lean_ctor_set(v___x_1369_, 2, v_v_1491_);
lean_ctor_set(v___x_1369_, 1, v_k_1490_);
lean_ctor_set(v___x_1369_, 0, v___x_1495_);
v___x_1499_ = v___x_1369_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1491_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1489_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_unsigned_to_nat(2u);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_impl_1375_);
lean_ctor_set(v___x_1369_, 3, v_r_1489_);
lean_ctor_set(v___x_1369_, 0, v___x_1506_);
v___x_1508_ = v___x_1369_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_r_1489_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_impl_1375_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v_v_1365_);
lean_dec(v_k_1364_);
v___x_1510_ = lean_box_uint64(v_k_1360_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 2, v_v_1361_);
lean_ctor_set(v___x_1369_, 1, v___x_1510_);
v___x_1512_ = v___x_1369_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_size_1363_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_l_1366_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_r_1367_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
lean_object* v_impl_1514_; lean_object* v___x_1515_; 
lean_dec(v_size_1363_);
v_impl_1514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_1360_, v_v_1361_, v_l_1366_);
v___x_1515_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1367_) == 0)
{
lean_object* v_size_1516_; lean_object* v_size_1517_; lean_object* v_k_1518_; lean_object* v_v_1519_; lean_object* v_l_1520_; lean_object* v_r_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v_size_1516_ = lean_ctor_get(v_r_1367_, 0);
v_size_1517_ = lean_ctor_get(v_impl_1514_, 0);
lean_inc(v_size_1517_);
v_k_1518_ = lean_ctor_get(v_impl_1514_, 1);
lean_inc(v_k_1518_);
v_v_1519_ = lean_ctor_get(v_impl_1514_, 2);
lean_inc(v_v_1519_);
v_l_1520_ = lean_ctor_get(v_impl_1514_, 3);
lean_inc(v_l_1520_);
v_r_1521_ = lean_ctor_get(v_impl_1514_, 4);
lean_inc(v_r_1521_);
v___x_1522_ = lean_unsigned_to_nat(3u);
v___x_1523_ = lean_nat_mul(v___x_1522_, v_size_1516_);
v___x_1524_ = lean_nat_dec_lt(v___x_1523_, v_size_1517_);
lean_dec(v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_dec(v_r_1521_);
lean_dec(v_l_1520_);
lean_dec(v_v_1519_);
lean_dec(v_k_1518_);
v___x_1525_ = lean_nat_add(v___x_1515_, v_size_1517_);
lean_dec(v_size_1517_);
v___x_1526_ = lean_nat_add(v___x_1525_, v_size_1516_);
lean_dec(v___x_1525_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 3, v_impl_1514_);
lean_ctor_set(v___x_1369_, 0, v___x_1526_);
v___x_1528_ = v___x_1369_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_impl_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1367_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1595_; 
v_isSharedCheck_1595_ = !lean_is_exclusive(v_impl_1514_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1596_ = lean_ctor_get(v_impl_1514_, 4);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_impl_1514_, 3);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1514_, 2);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1514_, 1);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1514_, 0);
lean_dec(v_unused_1600_);
v___x_1531_ = v_impl_1514_;
v_isShared_1532_ = v_isSharedCheck_1595_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v_impl_1514_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1595_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_size_1533_; lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v_l_1537_; lean_object* v_r_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_size_1533_ = lean_ctor_get(v_l_1520_, 0);
v_size_1534_ = lean_ctor_get(v_r_1521_, 0);
v_k_1535_ = lean_ctor_get(v_r_1521_, 1);
v_v_1536_ = lean_ctor_get(v_r_1521_, 2);
v_l_1537_ = lean_ctor_get(v_r_1521_, 3);
v_r_1538_ = lean_ctor_get(v_r_1521_, 4);
v___x_1539_ = lean_unsigned_to_nat(2u);
v___x_1540_ = lean_nat_mul(v___x_1539_, v_size_1533_);
v___x_1541_ = lean_nat_dec_lt(v_size_1534_, v___x_1540_);
lean_dec(v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1570_; 
lean_inc(v_r_1538_);
lean_inc(v_l_1537_);
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_r_1521_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; 
v_unused_1571_ = lean_ctor_get(v_r_1521_, 4);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_r_1521_, 3);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_r_1521_, 2);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_r_1521_, 1);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_r_1521_, 0);
lean_dec(v_unused_1575_);
v___x_1543_ = v_r_1521_;
v_isShared_1544_ = v_isSharedCheck_1570_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v_r_1521_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1570_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___x_1558_; lean_object* v___y_1560_; 
v___x_1545_ = lean_nat_add(v___x_1515_, v_size_1517_);
lean_dec(v_size_1517_);
v___x_1546_ = lean_nat_add(v___x_1545_, v_size_1516_);
lean_dec(v___x_1545_);
v___x_1558_ = lean_nat_add(v___x_1515_, v_size_1533_);
if (lean_obj_tag(v_l_1537_) == 0)
{
lean_object* v_size_1568_; 
v_size_1568_ = lean_ctor_get(v_l_1537_, 0);
lean_inc(v_size_1568_);
v___y_1560_ = v_size_1568_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___y_1560_ = v___x_1569_;
goto v___jp_1559_;
}
v___jp_1547_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_nat_add(v___y_1548_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec(v___y_1548_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1367_);
lean_ctor_set(v___x_1543_, 3, v_r_1538_);
lean_ctor_set(v___x_1543_, 2, v_v_1365_);
lean_ctor_set(v___x_1543_, 1, v_k_1364_);
lean_ctor_set(v___x_1543_, 0, v___x_1551_);
v___x_1553_ = v___x_1543_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_r_1538_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_r_1367_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 4, v___x_1553_);
lean_ctor_set(v___x_1531_, 3, v___y_1549_);
lean_ctor_set(v___x_1531_, 2, v_v_1536_);
lean_ctor_set(v___x_1531_, 1, v_k_1535_);
lean_ctor_set(v___x_1531_, 0, v___x_1546_);
v___x_1555_ = v___x_1531_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v___y_1549_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_nat_add(v___x_1558_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec(v___x_1558_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_l_1537_);
lean_ctor_set(v___x_1369_, 3, v_l_1520_);
lean_ctor_set(v___x_1369_, 2, v_v_1519_);
lean_ctor_set(v___x_1369_, 1, v_k_1518_);
lean_ctor_set(v___x_1369_, 0, v___x_1561_);
v___x_1563_ = v___x_1369_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1518_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1519_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_l_1520_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_l_1537_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_nat_add(v___x_1515_, v_size_1516_);
if (lean_obj_tag(v_r_1538_) == 0)
{
lean_object* v_size_1565_; 
v_size_1565_ = lean_ctor_get(v_r_1538_, 0);
lean_inc(v_size_1565_);
v___y_1548_ = v___x_1564_;
v___y_1549_ = v___x_1563_;
v___y_1550_ = v_size_1565_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
v___y_1548_ = v___x_1564_;
v___y_1549_ = v___x_1563_;
v___y_1550_ = v___x_1566_;
goto v___jp_1547_;
}
}
}
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_del_object(v___x_1369_);
v___x_1576_ = lean_nat_add(v___x_1515_, v_size_1517_);
lean_dec(v_size_1517_);
v___x_1577_ = lean_nat_add(v___x_1576_, v_size_1516_);
lean_dec(v___x_1576_);
v___x_1578_ = lean_nat_add(v___x_1515_, v_size_1516_);
v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1534_);
lean_dec(v___x_1578_);
lean_inc_ref(v_r_1367_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 4, v_r_1367_);
lean_ctor_set(v___x_1531_, 3, v_r_1521_);
lean_ctor_set(v___x_1531_, 2, v_v_1365_);
lean_ctor_set(v___x_1531_, 1, v_k_1364_);
lean_ctor_set(v___x_1531_, 0, v___x_1579_);
v___x_1581_ = v___x_1531_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_r_1521_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_r_1367_);
v___x_1581_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_isSharedCheck_1588_ = !lean_is_exclusive(v_r_1367_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; 
v_unused_1589_ = lean_ctor_get(v_r_1367_, 4);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_r_1367_, 3);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_r_1367_, 2);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_r_1367_, 1);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_r_1367_, 0);
lean_dec(v_unused_1593_);
v___x_1583_ = v_r_1367_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_r_1367_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___x_1581_);
lean_ctor_set(v___x_1583_, 3, v_l_1520_);
lean_ctor_set(v___x_1583_, 2, v_v_1519_);
lean_ctor_set(v___x_1583_, 1, v_k_1518_);
lean_ctor_set(v___x_1583_, 0, v___x_1577_);
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1518_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1519_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_l_1520_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v___x_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1601_; 
v_l_1601_ = lean_ctor_get(v_impl_1514_, 3);
lean_inc(v_l_1601_);
if (lean_obj_tag(v_l_1601_) == 0)
{
lean_object* v_r_1602_; lean_object* v_k_1603_; lean_object* v_v_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1615_; 
v_r_1602_ = lean_ctor_get(v_impl_1514_, 4);
v_k_1603_ = lean_ctor_get(v_impl_1514_, 1);
v_v_1604_ = lean_ctor_get(v_impl_1514_, 2);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_impl_1514_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1616_ = lean_ctor_get(v_impl_1514_, 3);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1514_, 0);
lean_dec(v_unused_1617_);
v___x_1606_ = v_impl_1514_;
v_isShared_1607_ = v_isSharedCheck_1615_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_r_1602_);
lean_inc(v_v_1604_);
lean_inc(v_k_1603_);
lean_dec(v_impl_1514_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1615_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1602_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 3, v_r_1602_);
lean_ctor_set(v___x_1606_, 2, v_v_1365_);
lean_ctor_set(v___x_1606_, 1, v_k_1364_);
lean_ctor_set(v___x_1606_, 0, v___x_1515_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_r_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_r_1602_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v___x_1610_);
lean_ctor_set(v___x_1369_, 3, v_l_1601_);
lean_ctor_set(v___x_1369_, 2, v_v_1604_);
lean_ctor_set(v___x_1369_, 1, v_k_1603_);
lean_ctor_set(v___x_1369_, 0, v___x_1608_);
v___x_1612_ = v___x_1369_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1603_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1604_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_l_1601_);
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
else
{
lean_object* v_r_1618_; 
v_r_1618_ = lean_ctor_get(v_impl_1514_, 4);
lean_inc(v_r_1618_);
if (lean_obj_tag(v_r_1618_) == 0)
{
lean_object* v_k_1619_; lean_object* v_v_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1643_; 
v_k_1619_ = lean_ctor_get(v_impl_1514_, 1);
v_v_1620_ = lean_ctor_get(v_impl_1514_, 2);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_impl_1514_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; lean_object* v_unused_1645_; lean_object* v_unused_1646_; 
v_unused_1644_ = lean_ctor_get(v_impl_1514_, 4);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_impl_1514_, 3);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_impl_1514_, 0);
lean_dec(v_unused_1646_);
v___x_1622_ = v_impl_1514_;
v_isShared_1623_ = v_isSharedCheck_1643_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_v_1620_);
lean_inc(v_k_1619_);
lean_dec(v_impl_1514_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1643_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1639_; 
v_k_1624_ = lean_ctor_get(v_r_1618_, 1);
v_v_1625_ = lean_ctor_get(v_r_1618_, 2);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_r_1618_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1640_ = lean_ctor_get(v_r_1618_, 4);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_r_1618_, 3);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_r_1618_, 0);
lean_dec(v_unused_1642_);
v___x_1627_ = v_r_1618_;
v_isShared_1628_ = v_isSharedCheck_1639_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_v_1625_);
lean_inc(v_k_1624_);
lean_dec(v_r_1618_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1639_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_unsigned_to_nat(3u);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v_l_1601_);
lean_ctor_set(v___x_1627_, 3, v_l_1601_);
lean_ctor_set(v___x_1627_, 2, v_v_1620_);
lean_ctor_set(v___x_1627_, 1, v_k_1619_);
lean_ctor_set(v___x_1627_, 0, v___x_1515_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1619_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1620_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_l_1601_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_l_1601_);
v___x_1631_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_l_1601_);
lean_ctor_set(v___x_1622_, 2, v_v_1365_);
lean_ctor_set(v___x_1622_, 1, v_k_1364_);
lean_ctor_set(v___x_1622_, 0, v___x_1515_);
v___x_1633_ = v___x_1622_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_l_1601_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_l_1601_);
v___x_1633_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v___x_1633_);
lean_ctor_set(v___x_1369_, 3, v___x_1631_);
lean_ctor_set(v___x_1369_, 2, v_v_1625_);
lean_ctor_set(v___x_1369_, 1, v_k_1624_);
lean_ctor_set(v___x_1369_, 0, v___x_1629_);
v___x_1635_ = v___x_1369_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_unsigned_to_nat(2u);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_r_1618_);
lean_ctor_set(v___x_1369_, 3, v_impl_1514_);
lean_ctor_set(v___x_1369_, 0, v___x_1647_);
v___x_1649_ = v___x_1369_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_impl_1514_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_r_1618_);
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
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_box_uint64(v_k_1360_);
v___x_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
lean_ctor_set(v___x_1654_, 2, v_v_1361_);
lean_ctor_set(v___x_1654_, 3, v_t_1362_);
lean_ctor_set(v___x_1654_, 4, v_t_1362_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(lean_object* v_k_1655_, lean_object* v_v_1656_, lean_object* v_t_1657_){
_start:
{
uint64_t v_k_boxed_1658_; lean_object* v_res_1659_; 
v_k_boxed_1658_ = lean_unbox_uint64(v_k_1655_);
lean_dec_ref(v_k_1655_);
v_res_1659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_1658_, v_v_1656_, v_t_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(lean_object* v_wi_1660_, lean_object* v_s_1661_){
_start:
{
uint64_t v_javascriptHash_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_javascriptHash_1662_ = lean_ctor_get_uint64(v_wi_1660_, sizeof(void*)*2);
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_wi_1660_);
v___x_1664_ = lean_box(0);
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_1661_, v_javascriptHash_1662_, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1663_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_1662_, v___x_1666_, v_s_1661_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(lean_object* v_wi_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v_env_1673_; lean_object* v_nextMacroScope_1674_; lean_object* v_ngen_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_traceState_1677_; lean_object* v_messages_1678_; lean_object* v_infoState_1679_; lean_object* v_snapshotTasks_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1709_; 
v___x_1672_ = lean_st_ref_take(v___y_1670_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
v_nextMacroScope_1674_ = lean_ctor_get(v___x_1672_, 1);
v_ngen_1675_ = lean_ctor_get(v___x_1672_, 2);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1672_, 3);
v_traceState_1677_ = lean_ctor_get(v___x_1672_, 4);
v_messages_1678_ = lean_ctor_get(v___x_1672_, 6);
v_infoState_1679_ = lean_ctor_get(v___x_1672_, 7);
v_snapshotTasks_1680_ = lean_ctor_get(v___x_1672_, 8);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v___x_1672_, 5);
lean_dec(v_unused_1710_);
v___x_1682_ = v___x_1672_;
v_isShared_1683_ = v_isSharedCheck_1709_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_snapshotTasks_1680_);
lean_inc(v_infoState_1679_);
lean_inc(v_messages_1678_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_ngen_1675_);
lean_inc(v_nextMacroScope_1674_);
lean_inc(v_env_1673_);
lean_dec(v___x_1672_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1709_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___f_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___f_1684_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1684_, 0, v_wi_1668_);
v___x_1685_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1686_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1685_, v_env_1673_, v___f_1684_);
v___x_1687_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 5, v___x_1687_);
lean_ctor_set(v___x_1682_, 0, v___x_1686_);
v___x_1689_ = v___x_1682_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_nextMacroScope_1674_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_ngen_1675_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1708_, 4, v_traceState_1677_);
lean_ctor_set(v_reuseFailAlloc_1708_, 5, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1708_, 6, v_messages_1678_);
lean_ctor_set(v_reuseFailAlloc_1708_, 7, v_infoState_1679_);
lean_ctor_set(v_reuseFailAlloc_1708_, 8, v_snapshotTasks_1680_);
v___x_1689_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_mctx_1692_; lean_object* v_zetaDeltaFVarIds_1693_; lean_object* v_postponed_1694_; lean_object* v_diag_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v___x_1690_ = lean_st_ref_set(v___y_1670_, v___x_1689_);
v___x_1691_ = lean_st_ref_take(v___y_1669_);
v_mctx_1692_ = lean_ctor_get(v___x_1691_, 0);
v_zetaDeltaFVarIds_1693_ = lean_ctor_get(v___x_1691_, 2);
v_postponed_1694_ = lean_ctor_get(v___x_1691_, 3);
v_diag_1695_ = lean_ctor_get(v___x_1691_, 4);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v___x_1691_, 1);
lean_dec(v_unused_1707_);
v___x_1697_ = v___x_1691_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_diag_1695_);
lean_inc(v_postponed_1694_);
lean_inc(v_zetaDeltaFVarIds_1693_);
lean_inc(v_mctx_1692_);
lean_dec(v___x_1691_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1699_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_mctx_1692_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_zetaDeltaFVarIds_1693_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_postponed_1694_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v_diag_1695_);
v___x_1701_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_st_ref_set(v___y_1669_, v___x_1701_);
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(lean_object* v_wi_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec(v___y_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(lean_object* v_ext_1716_, lean_object* v_b_1717_, uint8_t v_kind_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_currNamespace_1723_; lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v_nextMacroScope_1726_; lean_object* v_ngen_1727_; lean_object* v_auxDeclNGen_1728_; lean_object* v_traceState_1729_; lean_object* v_messages_1730_; lean_object* v_infoState_1731_; lean_object* v_snapshotTasks_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1759_; 
v_currNamespace_1723_ = lean_ctor_get(v___y_1720_, 6);
v___x_1724_ = lean_st_ref_take(v___y_1721_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
v_nextMacroScope_1726_ = lean_ctor_get(v___x_1724_, 1);
v_ngen_1727_ = lean_ctor_get(v___x_1724_, 2);
v_auxDeclNGen_1728_ = lean_ctor_get(v___x_1724_, 3);
v_traceState_1729_ = lean_ctor_get(v___x_1724_, 4);
v_messages_1730_ = lean_ctor_get(v___x_1724_, 6);
v_infoState_1731_ = lean_ctor_get(v___x_1724_, 7);
v_snapshotTasks_1732_ = lean_ctor_get(v___x_1724_, 8);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1724_, 5);
lean_dec(v_unused_1760_);
v___x_1734_ = v___x_1724_;
v_isShared_1735_ = v_isSharedCheck_1759_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snapshotTasks_1732_);
lean_inc(v_infoState_1731_);
lean_inc(v_messages_1730_);
lean_inc(v_traceState_1729_);
lean_inc(v_auxDeclNGen_1728_);
lean_inc(v_ngen_1727_);
lean_inc(v_nextMacroScope_1726_);
lean_inc(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1759_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_inc(v_currNamespace_1723_);
v___x_1736_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1725_, v_ext_1716_, v_b_1717_, v_kind_1718_, v_currNamespace_1723_);
v___x_1737_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 5, v___x_1737_);
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1739_ = v___x_1734_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_nextMacroScope_1726_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_ngen_1727_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_auxDeclNGen_1728_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_traceState_1729_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1758_, 6, v_messages_1730_);
lean_ctor_set(v_reuseFailAlloc_1758_, 7, v_infoState_1731_);
lean_ctor_set(v_reuseFailAlloc_1758_, 8, v_snapshotTasks_1732_);
v___x_1739_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_mctx_1742_; lean_object* v_zetaDeltaFVarIds_1743_; lean_object* v_postponed_1744_; lean_object* v_diag_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1756_; 
v___x_1740_ = lean_st_ref_set(v___y_1721_, v___x_1739_);
v___x_1741_ = lean_st_ref_take(v___y_1719_);
v_mctx_1742_ = lean_ctor_get(v___x_1741_, 0);
v_zetaDeltaFVarIds_1743_ = lean_ctor_get(v___x_1741_, 2);
v_postponed_1744_ = lean_ctor_get(v___x_1741_, 3);
v_diag_1745_ = lean_ctor_get(v___x_1741_, 4);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1741_, 1);
lean_dec(v_unused_1757_);
v___x_1747_ = v___x_1741_;
v_isShared_1748_ = v_isSharedCheck_1756_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_diag_1745_);
lean_inc(v_postponed_1744_);
lean_inc(v_zetaDeltaFVarIds_1743_);
lean_inc(v_mctx_1742_);
lean_dec(v___x_1741_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1756_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_mctx_1742_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_zetaDeltaFVarIds_1743_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_postponed_1744_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_diag_1745_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_st_ref_set(v___y_1719_, v___x_1751_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(lean_object* v_ext_1761_, lean_object* v_b_1762_, lean_object* v_kind_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v_kind_boxed_1768_; lean_object* v_res_1769_; 
v_kind_boxed_1768_ = lean_unbox(v_kind_1763_);
v_res_1769_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_1761_, v_b_1762_, v_kind_boxed_1768_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(uint64_t v_h_1770_, lean_object* v_n_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1779_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1780_ = lean_box_uint64(v_h_1770_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v_n_1771_);
v___x_1782_ = 2;
v___x_1783_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1779_, v___x_1781_, v___x_1782_, v___y_1775_, v___y_1776_, v___y_1777_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(lean_object* v_h_1784_, lean_object* v_n_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint64_t v_h_boxed_1793_; lean_object* v_res_1794_; 
v_h_boxed_1793_ = lean_unbox_uint64(v_h_1784_);
lean_dec_ref(v_h_1784_);
v_res_1794_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_h_boxed_1793_, v_n_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(uint64_t v_h_1795_, lean_object* v_n_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1804_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1805_ = lean_box_uint64(v_h_1795_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_n_1796_);
v___x_1807_ = 0;
v___x_1808_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_1804_, v___x_1806_, v___x_1807_, v___y_1800_, v___y_1801_, v___y_1802_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(lean_object* v_h_1809_, lean_object* v_n_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint64_t v_h_boxed_1818_; lean_object* v_res_1819_; 
v_h_boxed_1818_ = lean_unbox_uint64(v_h_1809_);
lean_dec_ref(v_h_1809_);
v_res_1819_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_h_boxed_1818_, v_n_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(lean_object* v_env_1820_, lean_object* v_declName_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v___x_1824_; lean_object* v_env_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; uint8_t v___x_1828_; 
v___x_1824_ = 0;
v_env_1825_ = l_Lean_Environment_setExporting(v_env_1820_, v___x_1824_);
lean_inc(v_declName_1821_);
v___x_1826_ = l_Lean_mkPrivateName(v_env_1825_, v_declName_1821_);
v___x_1827_ = 1;
lean_inc_ref(v_env_1825_);
v___x_1828_ = l_Lean_Environment_contains(v_env_1825_, v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = l_Lean_privateToUserName(v_declName_1821_);
v___x_1830_ = l_Lean_Environment_contains(v_env_1825_, v___x_1829_, v___x_1827_);
v___x_1831_ = lean_box(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___y_1823_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec_ref(v_env_1825_);
lean_dec(v_declName_1821_);
v___x_1833_ = lean_box(v___x_1828_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___y_1823_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(lean_object* v_env_1835_, lean_object* v_declName_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_1835_, v_declName_1836_, v___y_1837_, v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(lean_object* v_msgData_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; lean_object* v_env_1847_; lean_object* v___x_1848_; lean_object* v_mctx_1849_; lean_object* v_lctx_1850_; lean_object* v_options_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1846_ = lean_st_ref_get(v___y_1844_);
v_env_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc_ref(v_env_1847_);
lean_dec(v___x_1846_);
v___x_1848_ = lean_st_ref_get(v___y_1842_);
v_mctx_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref(v_mctx_1849_);
lean_dec(v___x_1848_);
v_lctx_1850_ = lean_ctor_get(v___y_1841_, 2);
v_options_1851_ = lean_ctor_get(v___y_1843_, 2);
lean_inc_ref(v_options_1851_);
lean_inc_ref(v_lctx_1850_);
v___x_1852_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1852_, 0, v_env_1847_);
lean_ctor_set(v___x_1852_, 1, v_mctx_1849_);
lean_ctor_set(v___x_1852_, 2, v_lctx_1850_);
lean_ctor_set(v___x_1852_, 3, v_options_1851_);
v___x_1853_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v_msgData_1840_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object* v_msgData_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1861_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1862_; double v___x_1863_; 
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_float_of_nat(v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1866_, lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_ref_1873_; lean_object* v___x_1874_; lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1919_; 
v_ref_1873_ = lean_ctor_get(v___y_1870_, 5);
v___x_1874_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1919_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1919_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v_traceState_1880_; lean_object* v_env_1881_; lean_object* v_nextMacroScope_1882_; lean_object* v_ngen_1883_; lean_object* v_auxDeclNGen_1884_; lean_object* v_cache_1885_; lean_object* v_messages_1886_; lean_object* v_infoState_1887_; lean_object* v_snapshotTasks_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1918_; 
v___x_1879_ = lean_st_ref_take(v___y_1871_);
v_traceState_1880_ = lean_ctor_get(v___x_1879_, 4);
v_env_1881_ = lean_ctor_get(v___x_1879_, 0);
v_nextMacroScope_1882_ = lean_ctor_get(v___x_1879_, 1);
v_ngen_1883_ = lean_ctor_get(v___x_1879_, 2);
v_auxDeclNGen_1884_ = lean_ctor_get(v___x_1879_, 3);
v_cache_1885_ = lean_ctor_get(v___x_1879_, 5);
v_messages_1886_ = lean_ctor_get(v___x_1879_, 6);
v_infoState_1887_ = lean_ctor_get(v___x_1879_, 7);
v_snapshotTasks_1888_ = lean_ctor_get(v___x_1879_, 8);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1890_ = v___x_1879_;
v_isShared_1891_ = v_isSharedCheck_1918_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snapshotTasks_1888_);
lean_inc(v_infoState_1887_);
lean_inc(v_messages_1886_);
lean_inc(v_cache_1885_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1884_);
lean_inc(v_ngen_1883_);
lean_inc(v_nextMacroScope_1882_);
lean_inc(v_env_1881_);
lean_dec(v___x_1879_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1918_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
uint64_t v_tid_1892_; lean_object* v_traces_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1917_; 
v_tid_1892_ = lean_ctor_get_uint64(v_traceState_1880_, sizeof(void*)*1);
v_traces_1893_ = lean_ctor_get(v_traceState_1880_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_traceState_1880_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1895_ = v_traceState_1880_;
v_isShared_1896_ = v_isSharedCheck_1917_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_traces_1893_);
lean_dec(v_traceState_1880_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1917_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; double v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1899_ = 0;
v___x_1900_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1901_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1901_, 0, v_cls_1866_);
lean_ctor_set(v___x_1901_, 1, v___x_1897_);
lean_ctor_set(v___x_1901_, 2, v___x_1900_);
lean_ctor_set_float(v___x_1901_, sizeof(void*)*3, v___x_1898_);
lean_ctor_set_float(v___x_1901_, sizeof(void*)*3 + 8, v___x_1898_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 16, v___x_1899_);
v___x_1902_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1903_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v_a_1875_);
lean_ctor_set(v___x_1903_, 2, v___x_1902_);
lean_inc(v_ref_1873_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_ref_1873_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_PersistentArray_push___redArg(v_traces_1893_, v___x_1904_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1905_);
v___x_1907_ = v___x_1895_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1905_);
lean_ctor_set_uint64(v_reuseFailAlloc_1916_, sizeof(void*)*1, v_tid_1892_);
v___x_1907_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 4, v___x_1907_);
v___x_1909_ = v___x_1890_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_env_1881_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_nextMacroScope_1882_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_ngen_1883_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_auxDeclNGen_1884_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_cache_1885_);
lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_messages_1886_);
lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_infoState_1887_);
lean_ctor_set(v_reuseFailAlloc_1915_, 8, v_snapshotTasks_1888_);
v___x_1909_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1910_ = lean_st_ref_set(v___y_1871_, v___x_1909_);
v___x_1911_ = lean_box(0);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1911_);
v___x_1913_ = v___x_1877_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1920_, lean_object* v_msg_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_1920_, v_msg_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(lean_object* v_as_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
if (lean_obj_tag(v_as_1931_) == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v_options_1941_; uint8_t v_hasTrace_1942_; 
v_options_1941_ = lean_ctor_get(v___y_1936_, 2);
v_hasTrace_1942_ = lean_ctor_get_uint8(v_options_1941_, sizeof(void*)*1);
if (v_hasTrace_1942_ == 0)
{
lean_object* v_tail_1943_; 
v_tail_1943_ = lean_ctor_get(v_as_1931_, 1);
lean_inc(v_tail_1943_);
lean_dec_ref_known(v_as_1931_, 2);
v_as_1931_ = v_tail_1943_;
goto _start;
}
else
{
lean_object* v_head_1945_; lean_object* v_tail_1946_; lean_object* v_fst_1947_; lean_object* v_snd_1948_; lean_object* v_inheritedTraceOptions_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_head_1945_ = lean_ctor_get(v_as_1931_, 0);
lean_inc(v_head_1945_);
v_tail_1946_ = lean_ctor_get(v_as_1931_, 1);
lean_inc(v_tail_1946_);
lean_dec_ref_known(v_as_1931_, 2);
v_fst_1947_ = lean_ctor_get(v_head_1945_, 0);
lean_inc_n(v_fst_1947_, 2);
v_snd_1948_ = lean_ctor_get(v_head_1945_, 1);
lean_inc(v_snd_1948_);
lean_dec(v_head_1945_);
v_inheritedTraceOptions_1949_ = lean_ctor_get(v___y_1936_, 13);
v___x_1950_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_1951_ = l_Lean_Name_append(v___x_1950_, v_fst_1947_);
v___x_1952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1949_, v_options_1941_, v___x_1951_);
lean_dec(v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec(v_snd_1948_);
lean_dec(v_fst_1947_);
v_as_1931_ = v_tail_1946_;
goto _start;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_snd_1948_);
v___x_1955_ = l_Lean_MessageData_ofFormat(v___x_1954_);
v___x_1956_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_1947_, v___x_1955_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_dec_ref_known(v___x_1956_, 1);
v_as_1931_ = v_tail_1946_;
goto _start;
}
else
{
lean_dec(v_tail_1946_);
return v___x_1956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_env_1967_, lean_object* v_currNamespace_1968_, lean_object* v_openDecls_1969_, lean_object* v_n_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = l_Lean_ResolveName_resolveNamespace(v_env_1967_, v_currNamespace_1968_, v_openDecls_1969_, v_n_1970_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_env_1975_, lean_object* v_currNamespace_1976_, lean_object* v_openDecls_1977_, lean_object* v_n_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_env_1975_, v_currNamespace_1976_, v_openDecls_1977_, v_n_1978_, v___y_1979_, v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object* v_opts_1982_, lean_object* v_opt_1983_){
_start:
{
lean_object* v_name_1984_; lean_object* v_defValue_1985_; lean_object* v_map_1986_; lean_object* v___x_1987_; 
v_name_1984_ = lean_ctor_get(v_opt_1983_, 0);
v_defValue_1985_ = lean_ctor_get(v_opt_1983_, 1);
v_map_1986_ = lean_ctor_get(v_opts_1982_, 0);
v___x_1987_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1986_, v_name_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_unbox(v_defValue_1985_);
return v___x_1988_;
}
else
{
lean_object* v_val_1989_; 
v_val_1989_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v___x_1987_, 1);
if (lean_obj_tag(v_val_1989_) == 1)
{
uint8_t v_v_1990_; 
v_v_1990_ = lean_ctor_get_uint8(v_val_1989_, 0);
lean_dec_ref_known(v_val_1989_, 0);
return v_v_1990_;
}
else
{
uint8_t v___x_1991_; 
lean_dec(v_val_1989_);
v___x_1991_ = lean_unbox(v_defValue_1985_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object* v_opts_1992_, lean_object* v_opt_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_1992_, v_opt_1993_);
lean_dec_ref(v_opt_1993_);
lean_dec_ref(v_opts_1992_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_box(1);
v___x_1997_ = l_Lean_MessageData_ofFormat(v___x_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2));
v___x_2002_ = l_Lean_MessageData_ofFormat(v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
if (lean_obj_tag(v_x_2004_) == 0)
{
return v_x_2003_;
}
else
{
lean_object* v_head_2005_; lean_object* v_tail_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2028_; 
v_head_2005_ = lean_ctor_get(v_x_2004_, 0);
v_tail_2006_ = lean_ctor_get(v_x_2004_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_x_2004_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2008_ = v_x_2004_;
v_isShared_2009_ = v_isSharedCheck_2028_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_tail_2006_);
lean_inc(v_head_2005_);
lean_dec(v_x_2004_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2028_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_before_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2026_; 
v_before_2010_ = lean_ctor_get(v_head_2005_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_head_2005_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v_head_2005_, 1);
lean_dec(v_unused_2027_);
v___x_2012_ = v_head_2005_;
v_isShared_2013_ = v_isSharedCheck_2026_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_before_2010_);
lean_dec(v_head_2005_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2026_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 7);
lean_ctor_set(v___x_2012_, 1, v___x_2014_);
lean_ctor_set(v___x_2012_, 0, v_x_2003_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_x_2003_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 7);
lean_ctor_set(v___x_2008_, 1, v___x_2017_);
lean_ctor_set(v___x_2008_, 0, v___x_2016_);
v___x_2019_ = v___x_2008_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_MessageData_ofSyntax(v_before_2010_);
v___x_2021_ = l_Lean_indentD(v___x_2020_);
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2019_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v_x_2003_ = v___x_2022_;
v_x_2004_ = v_tail_2006_;
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
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1));
v___x_2033_ = l_Lean_MessageData_ofFormat(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object* v_msgData_2034_, lean_object* v_macroStack_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_options_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; uint8_t v___x_2041_; 
v_options_2038_ = lean_ctor_get(v___y_2036_, 2);
v___x_2039_ = l_Lean_Elab_pp_macroStack;
v___x_2040_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_options_2038_, v___x_2039_);
v___x_2041_ = lean_bool_not(v___x_2040_);
if (v___x_2041_ == 0)
{
if (lean_obj_tag(v_macroStack_2035_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_msgData_2034_);
return v___x_2042_;
}
else
{
lean_object* v_head_2043_; lean_object* v_after_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2059_; 
v_head_2043_ = lean_ctor_get(v_macroStack_2035_, 0);
lean_inc(v_head_2043_);
v_after_2044_ = lean_ctor_get(v_head_2043_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_head_2043_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_head_2043_, 0);
lean_dec(v_unused_2060_);
v___x_2046_ = v_head_2043_;
v_isShared_2047_ = v_isSharedCheck_2059_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_after_2044_);
lean_dec(v_head_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2059_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 7);
lean_ctor_set(v___x_2046_, 1, v___x_2048_);
lean_ctor_set(v___x_2046_, 0, v_msgData_2034_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_msgData_2034_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_msgData_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2051_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = l_Lean_MessageData_ofSyntax(v_after_2044_);
v___x_2054_ = l_Lean_indentD(v___x_2053_);
v_msgData_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2055_, 0, v___x_2052_);
lean_ctor_set(v_msgData_2055_, 1, v___x_2054_);
v___x_2056_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_2055_, v_macroStack_2035_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v_macroStack_2035_);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_msgData_2034_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object* v_msgData_2062_, lean_object* v_macroStack_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2062_, v_macroStack_2063_, v___y_2064_);
lean_dec_ref(v___y_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_ref_2075_; lean_object* v___x_2076_; lean_object* v_a_2077_; lean_object* v_macroStack_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2089_; 
v_ref_2075_ = lean_ctor_get(v___y_2072_, 5);
v___x_2076_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_2067_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2076_);
v_macroStack_2078_ = lean_ctor_get(v___y_2068_, 1);
v___x_2079_ = l_Lean_Elab_getBetterRef(v_ref_2075_, v_macroStack_2078_);
lean_inc(v_macroStack_2078_);
v___x_2080_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_2077_, v_macroStack_2078_, v___y_2072_);
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2089_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2089_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2079_);
lean_ctor_set(v___x_2085_, 1, v_a_2081_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 1);
lean_ctor_set(v___x_2083_, 0, v___x_2085_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_fileName_2108_; lean_object* v_fileMap_2109_; lean_object* v_options_2110_; lean_object* v_currRecDepth_2111_; lean_object* v_maxRecDepth_2112_; lean_object* v_ref_2113_; lean_object* v_currNamespace_2114_; lean_object* v_openDecls_2115_; lean_object* v_initHeartbeats_2116_; lean_object* v_maxHeartbeats_2117_; lean_object* v_quotContext_2118_; lean_object* v_currMacroScope_2119_; uint8_t v_diag_2120_; lean_object* v_cancelTk_x3f_2121_; uint8_t v_suppressElabErrors_2122_; lean_object* v_inheritedTraceOptions_2123_; lean_object* v_ref_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_fileName_2108_ = lean_ctor_get(v___y_2105_, 0);
v_fileMap_2109_ = lean_ctor_get(v___y_2105_, 1);
v_options_2110_ = lean_ctor_get(v___y_2105_, 2);
v_currRecDepth_2111_ = lean_ctor_get(v___y_2105_, 3);
v_maxRecDepth_2112_ = lean_ctor_get(v___y_2105_, 4);
v_ref_2113_ = lean_ctor_get(v___y_2105_, 5);
v_currNamespace_2114_ = lean_ctor_get(v___y_2105_, 6);
v_openDecls_2115_ = lean_ctor_get(v___y_2105_, 7);
v_initHeartbeats_2116_ = lean_ctor_get(v___y_2105_, 8);
v_maxHeartbeats_2117_ = lean_ctor_get(v___y_2105_, 9);
v_quotContext_2118_ = lean_ctor_get(v___y_2105_, 10);
v_currMacroScope_2119_ = lean_ctor_get(v___y_2105_, 11);
v_diag_2120_ = lean_ctor_get_uint8(v___y_2105_, sizeof(void*)*14);
v_cancelTk_x3f_2121_ = lean_ctor_get(v___y_2105_, 12);
v_suppressElabErrors_2122_ = lean_ctor_get_uint8(v___y_2105_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2123_ = lean_ctor_get(v___y_2105_, 13);
v_ref_2124_ = l_Lean_replaceRef(v_ref_2099_, v_ref_2113_);
lean_inc_ref(v_inheritedTraceOptions_2123_);
lean_inc(v_cancelTk_x3f_2121_);
lean_inc(v_currMacroScope_2119_);
lean_inc(v_quotContext_2118_);
lean_inc(v_maxHeartbeats_2117_);
lean_inc(v_initHeartbeats_2116_);
lean_inc(v_openDecls_2115_);
lean_inc(v_currNamespace_2114_);
lean_inc(v_maxRecDepth_2112_);
lean_inc(v_currRecDepth_2111_);
lean_inc_ref(v_options_2110_);
lean_inc_ref(v_fileMap_2109_);
lean_inc_ref(v_fileName_2108_);
v___x_2125_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2125_, 0, v_fileName_2108_);
lean_ctor_set(v___x_2125_, 1, v_fileMap_2109_);
lean_ctor_set(v___x_2125_, 2, v_options_2110_);
lean_ctor_set(v___x_2125_, 3, v_currRecDepth_2111_);
lean_ctor_set(v___x_2125_, 4, v_maxRecDepth_2112_);
lean_ctor_set(v___x_2125_, 5, v_ref_2124_);
lean_ctor_set(v___x_2125_, 6, v_currNamespace_2114_);
lean_ctor_set(v___x_2125_, 7, v_openDecls_2115_);
lean_ctor_set(v___x_2125_, 8, v_initHeartbeats_2116_);
lean_ctor_set(v___x_2125_, 9, v_maxHeartbeats_2117_);
lean_ctor_set(v___x_2125_, 10, v_quotContext_2118_);
lean_ctor_set(v___x_2125_, 11, v_currMacroScope_2119_);
lean_ctor_set(v___x_2125_, 12, v_cancelTk_x3f_2121_);
lean_ctor_set(v___x_2125_, 13, v_inheritedTraceOptions_2123_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*14, v_diag_2120_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*14 + 1, v_suppressElabErrors_2122_);
v___x_2126_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___x_2125_, v___y_2106_);
lean_dec_ref_known(v___x_2125_, 14);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2127_, v_msg_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v_ref_2127_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2137_, lean_object* v_options_2138_, lean_object* v_currNamespace_2139_, lean_object* v_openDecls_2140_, lean_object* v_n_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = l_Lean_ResolveName_resolveGlobalName(v_env_2137_, v_options_2138_, v_currNamespace_2139_, v_openDecls_2140_, v_n_2141_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2146_, lean_object* v_options_2147_, lean_object* v_currNamespace_2148_, lean_object* v_openDecls_2149_, lean_object* v_n_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2146_, v_options_2147_, v_currNamespace_2148_, v_openDecls_2149_, v_n_2150_, v___y_2151_, v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec_ref(v_options_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object* v_keys_2154_, lean_object* v_i_2155_, lean_object* v_k_2156_){
_start:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_get_size(v_keys_2154_);
v___x_2158_ = lean_nat_dec_lt(v_i_2155_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_dec(v_i_2155_);
return v___x_2158_;
}
else
{
lean_object* v_k_x27_2159_; uint8_t v___x_2160_; 
v_k_x27_2159_ = lean_array_fget_borrowed(v_keys_2154_, v_i_2155_);
v___x_2160_ = l_Lean_instBEqExtraModUse_beq(v_k_2156_, v_k_x27_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(1u);
v___x_2162_ = lean_nat_add(v_i_2155_, v___x_2161_);
lean_dec(v_i_2155_);
v_i_2155_ = v___x_2162_;
goto _start;
}
else
{
lean_dec(v_i_2155_);
return v___x_2160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object* v_keys_2164_, lean_object* v_i_2165_, lean_object* v_k_2166_){
_start:
{
uint8_t v_res_2167_; lean_object* v_r_2168_; 
v_res_2167_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2164_, v_i_2165_, v_k_2166_);
lean_dec_ref(v_k_2166_);
lean_dec_ref(v_keys_2164_);
v_r_2168_ = lean_box(v_res_2167_);
return v_r_2168_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object* v_x_2169_, size_t v_x_2170_, lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_object* v_es_2172_; lean_object* v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; lean_object* v_j_2176_; lean_object* v___x_2177_; 
v_es_2172_ = lean_ctor_get(v_x_2169_, 0);
v___x_2173_ = lean_box(2);
v___x_2174_ = ((size_t)31ULL);
v___x_2175_ = lean_usize_land(v_x_2170_, v___x_2174_);
v_j_2176_ = lean_usize_to_nat(v___x_2175_);
v___x_2177_ = lean_array_get_borrowed(v___x_2173_, v_es_2172_, v_j_2176_);
lean_dec(v_j_2176_);
switch(lean_obj_tag(v___x_2177_))
{
case 0:
{
lean_object* v_key_2178_; uint8_t v___x_2179_; 
v_key_2178_ = lean_ctor_get(v___x_2177_, 0);
v___x_2179_ = l_Lean_instBEqExtraModUse_beq(v_x_2171_, v_key_2178_);
return v___x_2179_;
}
case 1:
{
lean_object* v_node_2180_; size_t v___x_2181_; size_t v___x_2182_; 
v_node_2180_ = lean_ctor_get(v___x_2177_, 0);
v___x_2181_ = ((size_t)5ULL);
v___x_2182_ = lean_usize_shift_right(v_x_2170_, v___x_2181_);
v_x_2169_ = v_node_2180_;
v_x_2170_ = v___x_2182_;
goto _start;
}
default: 
{
uint8_t v___x_2184_; 
v___x_2184_ = 0;
return v___x_2184_;
}
}
}
else
{
lean_object* v_ks_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_ks_2185_ = lean_ctor_get(v_x_2169_, 0);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_2185_, v___x_2186_, v_x_2171_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
size_t v_x_33537__boxed_2191_; uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_x_33537__boxed_2191_ = lean_unbox_usize(v_x_2189_);
lean_dec(v_x_2189_);
v_res_2192_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2188_, v_x_33537__boxed_2191_, v_x_2190_);
lean_dec_ref(v_x_2190_);
lean_dec_ref(v_x_2188_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
uint64_t v___x_2196_; size_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2196_ = l_Lean_instHashableExtraModUse_hash(v_x_2195_);
v___x_2197_ = lean_uint64_to_usize(v___x_2196_);
v___x_2198_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2194_, v___x_2197_, v_x_2195_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_res_2201_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2199_, v_x_2200_);
lean_dec_ref(v_x_2200_);
lean_dec_ref(v_x_2199_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1));
v___x_2206_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0));
v___x_2207_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7));
v___x_2216_ = l_Lean_stringToMessageData(v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v_cls_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_cls_2219_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4));
v___x_2220_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2221_ = l_Lean_Name_append(v___x_2220_, v_cls_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2232_, uint8_t v_isMeta_2233_, lean_object* v_hint_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_env_2243_; uint8_t v_isExporting_2244_; lean_object* v___x_2245_; lean_object* v_env_2246_; lean_object* v___x_2247_; lean_object* v_entry_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___x_2294_; uint8_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2242_ = lean_st_ref_get(v___y_2240_);
v_env_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2243_);
lean_dec(v___x_2242_);
v_isExporting_2244_ = lean_ctor_get_uint8(v_env_2243_, sizeof(void*)*8);
lean_dec_ref(v_env_2243_);
v___x_2245_ = lean_st_ref_get(v___y_2240_);
v_env_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_ref(v_env_2246_);
lean_dec(v___x_2245_);
v___x_2247_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2);
lean_inc(v_mod_2232_);
v_entry_2248_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2248_, 0, v_mod_2232_);
lean_ctor_set_uint8(v_entry_2248_, sizeof(void*)*1, v_isExporting_2244_);
lean_ctor_set_uint8(v_entry_2248_, sizeof(void*)*1 + 1, v_isMeta_2233_);
v___x_2249_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2250_ = lean_box(1);
v___x_2251_ = lean_box(0);
v___x_2294_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2247_, v___x_2249_, v_env_2246_, v___x_2250_, v___x_2251_);
v___x_2295_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_2294_, v_entry_2248_);
lean_dec(v___x_2294_);
v___x_2296_ = lean_bool_not(v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref_known(v_entry_2248_, 1);
lean_dec(v_hint_2234_);
lean_dec(v_mod_2232_);
v___x_2297_ = lean_box(0);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
else
{
lean_object* v_options_2299_; uint8_t v_hasTrace_2300_; 
v_options_2299_ = lean_ctor_get(v___y_2239_, 2);
v_hasTrace_2300_ = lean_ctor_get_uint8(v_options_2299_, sizeof(void*)*1);
if (v_hasTrace_2300_ == 0)
{
lean_dec(v_hint_2234_);
lean_dec(v_mod_2232_);
v___y_2253_ = v___y_2238_;
v___y_2254_ = v___y_2240_;
goto v___jp_2252_;
}
else
{
lean_object* v_inheritedTraceOptions_2301_; lean_object* v_cls_2302_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_inheritedTraceOptions_2301_ = lean_ctor_get(v___y_2239_, 13);
v_cls_2302_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4));
v___x_2322_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
v___x_2323_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2301_, v_options_2299_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_dec(v_hint_2234_);
lean_dec(v_mod_2232_);
v___y_2253_ = v___y_2238_;
v___y_2254_ = v___y_2240_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2324_; lean_object* v___y_2326_; 
v___x_2324_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
if (v_isExporting_2244_ == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17));
v___y_2326_ = v___x_2333_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2334_; 
v___x_2334_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18));
v___y_2326_ = v___x_2334_;
goto v___jp_2325_;
}
v___jp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_inc_ref(v___y_2326_);
v___x_2327_ = l_Lean_stringToMessageData(v___y_2326_);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2324_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
if (v_isMeta_2233_ == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2309_ = v___x_2330_;
v___y_2310_ = v___x_2331_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2309_ = v___x_2330_;
v___y_2310_ = v___x_2332_;
goto v___jp_2308_;
}
}
}
v___jp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___y_2304_);
lean_ctor_set(v___x_2306_, 1, v___y_2305_);
v___x_2307_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2302_, v___x_2306_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_dec_ref_known(v___x_2307_, 1);
v___y_2253_ = v___y_2238_;
v___y_2254_ = v___y_2240_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_entry_2248_, 1);
return v___x_2307_;
}
}
v___jp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
lean_inc_ref(v___y_2310_);
v___x_2311_ = l_Lean_stringToMessageData(v___y_2310_);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___y_2309_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = l_Lean_MessageData_ofName(v_mod_2232_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_Name_isAnonymous(v_hint_2234_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2319_ = l_Lean_MessageData_ofName(v_hint_2234_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___y_2304_ = v___x_2316_;
v___y_2305_ = v___x_2320_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2321_; 
lean_dec(v_hint_2234_);
v___x_2321_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9);
v___y_2304_ = v___x_2316_;
v___y_2305_ = v___x_2321_;
goto v___jp_2303_;
}
}
}
}
v___jp_2252_:
{
lean_object* v___x_2255_; lean_object* v_toEnvExtension_2256_; lean_object* v_env_2257_; lean_object* v_nextMacroScope_2258_; lean_object* v_ngen_2259_; lean_object* v_auxDeclNGen_2260_; lean_object* v_traceState_2261_; lean_object* v_messages_2262_; lean_object* v_infoState_2263_; lean_object* v_snapshotTasks_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2292_; 
v___x_2255_ = lean_st_ref_take(v___y_2254_);
v_toEnvExtension_2256_ = lean_ctor_get(v___x_2249_, 0);
v_env_2257_ = lean_ctor_get(v___x_2255_, 0);
v_nextMacroScope_2258_ = lean_ctor_get(v___x_2255_, 1);
v_ngen_2259_ = lean_ctor_get(v___x_2255_, 2);
v_auxDeclNGen_2260_ = lean_ctor_get(v___x_2255_, 3);
v_traceState_2261_ = lean_ctor_get(v___x_2255_, 4);
v_messages_2262_ = lean_ctor_get(v___x_2255_, 6);
v_infoState_2263_ = lean_ctor_get(v___x_2255_, 7);
v_snapshotTasks_2264_ = lean_ctor_get(v___x_2255_, 8);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; 
v_unused_2293_ = lean_ctor_get(v___x_2255_, 5);
lean_dec(v_unused_2293_);
v___x_2266_ = v___x_2255_;
v_isShared_2267_ = v_isSharedCheck_2292_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_snapshotTasks_2264_);
lean_inc(v_infoState_2263_);
lean_inc(v_messages_2262_);
lean_inc(v_traceState_2261_);
lean_inc(v_auxDeclNGen_2260_);
lean_inc(v_ngen_2259_);
lean_inc(v_nextMacroScope_2258_);
lean_inc(v_env_2257_);
lean_dec(v___x_2255_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2292_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_asyncMode_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v_asyncMode_2268_ = lean_ctor_get(v_toEnvExtension_2256_, 2);
v___x_2269_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2249_, v_env_2257_, v_entry_2248_, v_asyncMode_2268_, v___x_2251_);
v___x_2270_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 5, v___x_2270_);
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2272_ = v___x_2266_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_nextMacroScope_2258_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_ngen_2259_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_auxDeclNGen_2260_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_traceState_2261_);
lean_ctor_set(v_reuseFailAlloc_2291_, 5, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2291_, 6, v_messages_2262_);
lean_ctor_set(v_reuseFailAlloc_2291_, 7, v_infoState_2263_);
lean_ctor_set(v_reuseFailAlloc_2291_, 8, v_snapshotTasks_2264_);
v___x_2272_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_mctx_2275_; lean_object* v_zetaDeltaFVarIds_2276_; lean_object* v_postponed_2277_; lean_object* v_diag_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2289_; 
v___x_2273_ = lean_st_ref_set(v___y_2254_, v___x_2272_);
v___x_2274_ = lean_st_ref_take(v___y_2253_);
v_mctx_2275_ = lean_ctor_get(v___x_2274_, 0);
v_zetaDeltaFVarIds_2276_ = lean_ctor_get(v___x_2274_, 2);
v_postponed_2277_ = lean_ctor_get(v___x_2274_, 3);
v_diag_2278_ = lean_ctor_get(v___x_2274_, 4);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v___x_2274_, 1);
lean_dec(v_unused_2290_);
v___x_2280_ = v___x_2274_;
v_isShared_2281_ = v_isSharedCheck_2289_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_diag_2278_);
lean_inc(v_postponed_2277_);
lean_inc(v_zetaDeltaFVarIds_2276_);
lean_inc(v_mctx_2275_);
lean_dec(v___x_2274_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2289_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v___x_2282_);
v___x_2284_ = v___x_2280_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_mctx_2275_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_zetaDeltaFVarIds_2276_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_postponed_2277_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_diag_2278_);
v___x_2284_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_st_ref_set(v___y_2253_, v___x_2284_);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2335_, lean_object* v_isMeta_2336_, lean_object* v_hint_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v_isMeta_boxed_2345_; lean_object* v_res_2346_; 
v_isMeta_boxed_2345_ = lean_unbox(v_isMeta_2336_);
v_res_2346_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2335_, v_isMeta_boxed_2345_, v_hint_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2347_, lean_object* v_declName_2348_, lean_object* v_as_2349_, size_t v_sz_2350_, size_t v_i_2351_, lean_object* v_b_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2351_, v_sz_2350_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
lean_dec(v_declName_2348_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_b_2352_);
return v___x_2361_;
}
else
{
lean_object* v___x_2362_; lean_object* v_modules_2363_; lean_object* v___x_2364_; lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v_toImport_2367_; lean_object* v_module_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2362_ = l_Lean_Environment_header(v___x_2347_);
v_modules_2363_ = lean_ctor_get(v___x_2362_, 3);
lean_inc_ref(v_modules_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2365_ = lean_array_uget_borrowed(v_as_2349_, v_i_2351_);
v___x_2366_ = lean_array_get(v___x_2364_, v_modules_2363_, v_a_2365_);
lean_dec_ref(v_modules_2363_);
v_toImport_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_ref(v_toImport_2367_);
lean_dec(v___x_2366_);
v_module_2368_ = lean_ctor_get(v_toImport_2367_, 0);
lean_inc(v_module_2368_);
lean_dec_ref(v_toImport_2367_);
v___x_2369_ = 0;
lean_inc(v_declName_2348_);
v___x_2370_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2368_, v___x_2369_, v_declName_2348_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; 
lean_dec_ref_known(v___x_2370_, 1);
v___x_2371_ = lean_box(0);
v___x_2372_ = ((size_t)1ULL);
v___x_2373_ = lean_usize_add(v_i_2351_, v___x_2372_);
v_i_2351_ = v___x_2373_;
v_b_2352_ = v___x_2371_;
goto _start;
}
else
{
lean_dec(v_declName_2348_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2375_, lean_object* v_declName_2376_, lean_object* v_as_2377_, lean_object* v_sz_2378_, lean_object* v_i_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
size_t v_sz_boxed_2388_; size_t v_i_boxed_2389_; lean_object* v_res_2390_; 
v_sz_boxed_2388_ = lean_unbox_usize(v_sz_2378_);
lean_dec(v_sz_2378_);
v_i_boxed_2389_ = lean_unbox_usize(v_i_2379_);
lean_dec(v_i_2379_);
v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2375_, v_declName_2376_, v_as_2377_, v_sz_boxed_2388_, v_i_boxed_2389_, v_b_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_as_2377_);
lean_dec_ref(v___x_2375_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object* v_a_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_box(0);
return v___x_2393_;
}
else
{
lean_object* v_key_2394_; lean_object* v_value_2395_; lean_object* v_tail_2396_; uint8_t v___x_2397_; 
v_key_2394_ = lean_ctor_get(v_x_2392_, 0);
v_value_2395_ = lean_ctor_get(v_x_2392_, 1);
v_tail_2396_ = lean_ctor_get(v_x_2392_, 2);
v___x_2397_ = lean_name_eq(v_key_2394_, v_a_2391_);
if (v___x_2397_ == 0)
{
v_x_2392_ = v_tail_2396_;
goto _start;
}
else
{
lean_object* v___x_2399_; 
lean_inc(v_value_2395_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_value_2395_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object* v_a_2400_, lean_object* v_x_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2400_, v_x_2401_);
lean_dec(v_x_2401_);
lean_dec(v_a_2400_);
return v_res_2402_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2403_; uint64_t v___x_2404_; 
v___x_2403_ = lean_unsigned_to_nat(1723u);
v___x_2404_ = lean_uint64_of_nat(v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_buckets_2407_; lean_object* v___x_2408_; uint64_t v___y_2410_; 
v_buckets_2407_ = lean_ctor_get(v_m_2405_, 1);
v___x_2408_ = lean_array_get_size(v_buckets_2407_);
if (lean_obj_tag(v_a_2406_) == 0)
{
uint64_t v___x_2424_; 
v___x_2424_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0);
v___y_2410_ = v___x_2424_;
goto v___jp_2409_;
}
else
{
uint64_t v_hash_2425_; 
v_hash_2425_ = lean_ctor_get_uint64(v_a_2406_, sizeof(void*)*2);
v___y_2410_ = v_hash_2425_;
goto v___jp_2409_;
}
v___jp_2409_:
{
uint64_t v___x_2411_; uint64_t v___x_2412_; uint64_t v_fold_2413_; uint64_t v___x_2414_; uint64_t v___x_2415_; uint64_t v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; size_t v___x_2419_; size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2411_ = 32ULL;
v___x_2412_ = lean_uint64_shift_right(v___y_2410_, v___x_2411_);
v_fold_2413_ = lean_uint64_xor(v___y_2410_, v___x_2412_);
v___x_2414_ = 16ULL;
v___x_2415_ = lean_uint64_shift_right(v_fold_2413_, v___x_2414_);
v___x_2416_ = lean_uint64_xor(v_fold_2413_, v___x_2415_);
v___x_2417_ = lean_uint64_to_usize(v___x_2416_);
v___x_2418_ = lean_usize_of_nat(v___x_2408_);
v___x_2419_ = ((size_t)1ULL);
v___x_2420_ = lean_usize_sub(v___x_2418_, v___x_2419_);
v___x_2421_ = lean_usize_land(v___x_2417_, v___x_2420_);
v___x_2422_ = lean_array_uget_borrowed(v_buckets_2407_, v___x_2421_);
v___x_2423_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2406_, v___x_2422_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2426_, v_a_2427_);
lean_dec(v_a_2427_);
lean_dec_ref(v_m_2426_);
return v_res_2428_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___x_2432_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0));
v___x_2433_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2432_, v___x_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2436_, uint8_t v_isMeta_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v_env_2449_; lean_object* v___y_2451_; lean_object* v___x_2464_; 
v___x_2445_ = lean_st_ref_get(v___y_2443_);
v_env_2449_ = lean_ctor_get(v___x_2445_, 0);
lean_inc_ref(v_env_2449_);
lean_dec(v___x_2445_);
v___x_2464_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2449_, v_declName_2436_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_dec_ref(v_env_2449_);
lean_dec(v_declName_2436_);
goto v___jp_2446_;
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2466_; lean_object* v_modules_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v_val_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = l_Lean_Environment_header(v_env_2449_);
v_modules_2467_ = lean_ctor_get(v___x_2466_, 3);
lean_inc_ref(v_modules_2467_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = lean_array_get_size(v_modules_2467_);
v___x_2469_ = lean_nat_dec_lt(v_val_2465_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_dec_ref(v_modules_2467_);
lean_dec(v_val_2465_);
lean_dec_ref(v_env_2449_);
lean_dec(v_declName_2436_);
goto v___jp_2446_;
}
else
{
lean_object* v___x_2470_; lean_object* v_env_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___y_2475_; 
v___x_2470_ = lean_st_ref_get(v___y_2443_);
v_env_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_ref(v_env_2471_);
lean_dec(v___x_2470_);
v___x_2472_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2);
v___x_2473_ = lean_array_fget(v_modules_2467_, v_val_2465_);
lean_dec(v_val_2465_);
lean_dec_ref(v_modules_2467_);
if (v_isMeta_2437_ == 0)
{
lean_dec_ref(v_env_2471_);
v___y_2475_ = v_isMeta_2437_;
goto v___jp_2474_;
}
else
{
uint8_t v___x_2486_; uint8_t v___x_2487_; 
lean_inc(v_declName_2436_);
v___x_2486_ = l_Lean_isMarkedMeta(v_env_2471_, v_declName_2436_);
v___x_2487_ = lean_bool_not(v___x_2486_);
v___y_2475_ = v___x_2487_;
goto v___jp_2474_;
}
v___jp_2474_:
{
lean_object* v_toImport_2476_; lean_object* v_module_2477_; lean_object* v___x_2478_; 
v_toImport_2476_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_toImport_2476_);
lean_dec(v___x_2473_);
v_module_2477_ = lean_ctor_get(v_toImport_2476_, 0);
lean_inc(v_module_2477_);
lean_dec_ref(v_toImport_2476_);
lean_inc(v_declName_2436_);
v___x_2478_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2477_, v___y_2475_, v_declName_2436_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref_known(v___x_2478_, 1);
v___x_2479_ = l_Lean_indirectModUseExt;
v___x_2480_ = lean_box(1);
v___x_2481_ = lean_box(0);
lean_inc_ref(v_env_2449_);
v___x_2482_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2472_, v___x_2479_, v_env_2449_, v___x_2480_, v___x_2481_);
v___x_2483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2482_, v_declName_2436_);
lean_dec(v___x_2482_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3));
v___y_2451_ = v___x_2484_;
goto v___jp_2450_;
}
else
{
lean_object* v_val_2485_; 
v_val_2485_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2485_);
lean_dec_ref_known(v___x_2483_, 1);
v___y_2451_ = v_val_2485_;
goto v___jp_2450_;
}
}
else
{
lean_dec_ref(v_env_2449_);
lean_dec(v_declName_2436_);
return v___x_2478_;
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; size_t v_sz_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = lean_box(0);
v_sz_2453_ = lean_array_size(v___y_2451_);
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2449_, v_declName_2436_, v___y_2451_, v_sz_2453_, v___x_2454_, v___x_2452_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec_ref(v___y_2451_);
lean_dec_ref(v_env_2449_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2463_);
v___x_2457_ = v___x_2455_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_dec(v___x_2455_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2452_);
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2452_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2488_, lean_object* v_isMeta_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v_isMeta_boxed_2497_; lean_object* v_res_2498_; 
v_isMeta_boxed_2497_ = lean_unbox(v_isMeta_2489_);
v_res_2498_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2488_, v_isMeta_boxed_2497_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
if (lean_obj_tag(v_as_x27_2499_) == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_b_2500_);
return v___x_2508_;
}
else
{
lean_object* v_head_2509_; lean_object* v_tail_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; 
v_head_2509_ = lean_ctor_get(v_as_x27_2499_, 0);
v_tail_2510_ = lean_ctor_get(v_as_x27_2499_, 1);
v___x_2511_ = 1;
lean_inc(v_head_2509_);
v___x_2512_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2509_, v___x_2511_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; 
lean_dec_ref_known(v___x_2512_, 1);
v___x_2513_ = lean_box(0);
v_as_x27_2499_ = v_tail_2510_;
v_b_2500_ = v___x_2513_;
goto _start;
}
else
{
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2515_, lean_object* v_b_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2515_, v_b_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v_as_x27_2515_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_currNamespace_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_currNamespace_2525_);
lean_ctor_set(v___x_2528_, 1, v___y_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_currNamespace_2529_, v___y_2530_, v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_2533_, lean_object* v___y_2534_){
_start:
{
if (lean_obj_tag(v_x_2533_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; 
v_a_2535_ = lean_ctor_get(v_x_2533_, 0);
lean_inc(v_a_2535_);
v___x_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_a_2535_);
lean_ctor_set(v___x_2536_, 1, v___y_2534_);
return v___x_2536_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
v_a_2537_ = lean_ctor_get(v_x_2533_, 0);
lean_inc(v_a_2537_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v_a_2537_);
lean_ctor_set(v___x_2538_, 1, v___y_2534_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2539_, v___y_2540_);
lean_dec_ref(v_x_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2542_, lean_object* v_stx_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2542_, v_stx_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
if (lean_obj_tag(v_a_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2556_; 
v_a_2548_ = lean_ctor_get(v___x_2546_, 1);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2557_);
v___x_2550_ = v___x_2546_;
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2546_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_box(0);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_a_2548_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
lean_object* v_val_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2586_; 
v_val_2558_ = lean_ctor_get(v_a_2547_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_a_2547_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2560_ = v_a_2547_;
v_isShared_2561_ = v_isSharedCheck_2586_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_val_2558_);
lean_dec(v_a_2547_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2586_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_snd_2562_; 
v_snd_2562_ = lean_ctor_get(v_val_2558_, 1);
lean_inc(v_snd_2562_);
lean_dec(v_val_2558_);
if (lean_obj_tag(v_snd_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2572_; 
lean_del_object(v___x_2560_);
v_a_2563_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2546_, 2);
v_a_2564_ = lean_ctor_get(v_snd_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_snd_2562_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2566_ = v_snd_2562_;
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v_snd_2562_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2569_, v_a_2563_);
lean_dec_ref(v___x_2569_);
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2585_; 
v_a_2573_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2546_, 2);
v_a_2574_ = lean_ctor_get(v_snd_2562_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_snd_2562_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2576_ = v_snd_2562_;
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v_snd_2562_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_a_2574_);
v___x_2579_ = v___x_2560_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2579_);
v___x_2581_ = v___x_2576_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2581_, v_a_2573_);
lean_dec_ref(v___x_2581_);
return v___x_2582_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2587_ = lean_ctor_get(v___x_2546_, 0);
v_a_2588_ = lean_ctor_get(v___x_2546_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2546_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_inc(v_a_2587_);
lean_dec(v___x_2546_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2587_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2596_, lean_object* v_stx_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2596_, v_stx_2597_, v___y_2598_, v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2600_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = l_Lean_maxRecDepthErrorMessage;
v___x_2607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2609_ = l_Lean_MessageData_ofFormat(v___x_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2611_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2612_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_ref_2613_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; lean_object* v_env_2631_; lean_object* v_options_2632_; lean_object* v_currRecDepth_2633_; lean_object* v_maxRecDepth_2634_; lean_object* v_ref_2635_; lean_object* v_currNamespace_2636_; lean_object* v_openDecls_2637_; lean_object* v_quotContext_2638_; lean_object* v_currMacroScope_2639_; lean_object* v___x_2640_; lean_object* v_nextMacroScope_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v_methods_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2630_ = lean_st_ref_get(v___y_2628_);
v_env_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc_ref_n(v_env_2631_, 4);
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
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2642_, 0, v_env_2631_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2643_, 0, v_env_2631_);
lean_inc_n(v_openDecls_2637_, 2);
lean_inc_n(v_currNamespace_2636_, 3);
v___f_2644_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2644_, 0, v_env_2631_);
lean_closure_set(v___f_2644_, 1, v_currNamespace_2636_);
lean_closure_set(v___f_2644_, 2, v_openDecls_2637_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2645_, 0, v_currNamespace_2636_);
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
lean_dec_ref_known(v___x_2651_, 2);
v_macroScope_2654_ = lean_ctor_get(v_a_2652_, 0);
lean_inc(v_macroScope_2654_);
v_traceMsgs_2655_ = lean_ctor_get(v_a_2652_, 1);
lean_inc(v_traceMsgs_2655_);
v_expandedMacroDecls_2656_ = lean_ctor_get(v_a_2652_, 2);
lean_inc(v_expandedMacroDecls_2656_);
lean_dec(v_a_2652_);
v___x_2657_ = lean_box(0);
v___x_2658_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2656_, v___x_2657_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v_expandedMacroDecls_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2659_; lean_object* v_env_2660_; lean_object* v_ngen_2661_; lean_object* v_auxDeclNGen_2662_; lean_object* v_traceState_2663_; lean_object* v_cache_2664_; lean_object* v_messages_2665_; lean_object* v_infoState_2666_; lean_object* v_snapshotTasks_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref_known(v___x_2658_, 1);
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
v___x_2675_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2674_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
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
lean_dec_ref_known(v___x_2651_, 2);
if (lean_obj_tag(v_a_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v_a_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_a_2704_ = lean_ctor_get(v_a_2703_, 0);
lean_inc(v_a_2704_);
v_a_2705_ = lean_ctor_get(v_a_2703_, 1);
lean_inc_ref(v_a_2705_);
lean_dec_ref_known(v_a_2703_, 2);
v___x_2706_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2707_ = lean_string_dec_eq(v_a_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2705_);
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
v___x_2710_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2704_, v___x_2709_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v_a_2704_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; 
lean_dec_ref(v_a_2705_);
v___x_2711_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2704_);
return v___x_2711_;
}
}
else
{
lean_object* v___x_2712_; 
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
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
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
lean_dec_ref_known(v___x_2764_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
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
lean_dec_ref_known(v___x_2772_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
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
lean_dec_ref_known(v___x_2776_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
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
lean_dec_ref_known(v___x_2780_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
return v___x_2780_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2781_, 0, v___x_2773_);
v___x_2782_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2781_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_Widget_elabWidgetInstanceSpec(v___x_2777_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc_n(v_a_2785_, 2);
lean_dec_ref_known(v___x_2784_, 1);
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
lean_dec_ref_known(v___x_2786_, 1);
v___x_2789_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2788_, v___y_2749_, v___y_2751_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref_known(v___x_2789_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
return v___x_2789_;
}
}
else
{
lean_object* v_a_2790_; lean_object* v_id_2791_; uint64_t v_javascriptHash_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2790_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2786_, 1);
v_id_2791_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_id_2791_);
v_javascriptHash_2792_ = lean_ctor_get_uint64(v_a_2790_, sizeof(void*)*2);
lean_dec(v_a_2790_);
v___x_2793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1));
v___x_2794_ = l_Lean_Name_append(v_id_2791_, v___x_2793_);
v___x_2795_ = l_Lean_Core_mkFreshUserName(v___x_2794_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2797_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v___x_2797_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2785_, v___y_2749_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___x_2818_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = lean_box(0);
v___x_2818_ = l_Lean_Expr_hasMVar(v_a_2798_);
if (v___x_2818_ == 0)
{
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
v___x_2822_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2821_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_dec_ref_known(v___x_2822_, 1);
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
return v___x_2822_;
}
}
v___jp_2800_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
lean_inc_n(v_a_2796_, 2);
v___x_2808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2808_, 0, v_a_2796_);
lean_ctor_set(v___x_2808_, 1, v___x_2799_);
lean_ctor_set(v___x_2808_, 2, v___x_2807_);
v___x_2809_ = lean_box(0);
v___x_2810_ = 1;
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
v___x_2814_ = l_Lean_addAndCompile(v___x_2813_, v___x_2741_, v___x_2769_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2814_) == 0)
{
uint8_t v___x_2815_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = lean_unbox(v_a_2783_);
lean_dec(v_a_2783_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_2792_, v_a_2796_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_dec_ref_known(v___x_2816_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
return v___x_2816_;
}
}
else
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_2792_, v_a_2796_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_dec_ref_known(v___x_2817_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
return v___x_2817_;
}
}
}
else
{
lean_dec(v_a_2796_);
lean_dec(v_a_2783_);
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2783_);
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
lean_dec_ref_known(v___x_2866_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
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
lean_inc_n(v___x_2871_, 2);
v___x_2877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2871_);
lean_ctor_set(v___x_2877_, 1, v___x_2873_);
lean_ctor_set(v___x_2877_, 2, v___x_2875_);
lean_ctor_set(v___x_2877_, 3, v___x_2876_);
v___x_2878_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2879_ = l_Lean_Syntax_node1(v___x_2871_, v___x_2878_, v___x_2863_);
v___x_2880_ = l_Lean_Syntax_node2(v___x_2871_, v___x_2872_, v___x_2877_, v___x_2879_);
v___x_2881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2882_ = l_Lean_Elab_Term_elabTerm(v___x_2880_, v___x_2881_, v___x_2741_, v___x_2741_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2883_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; uint64_t v_javascriptHash_2886_; lean_object* v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v_javascriptHash_2886_ = lean_ctor_get_uint64(v_a_2885_, sizeof(void*)*1);
lean_dec(v_a_2885_);
v___x_2887_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2886_, v___y_2749_, v___y_2751_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_dec_ref_known(v___x_2887_, 1);
v_a_2754_ = v___x_2761_;
goto v___jp_2753_;
}
else
{
return v___x_2887_;
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
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
uint8_t v___x_34550__boxed_2916_; size_t v_sz_boxed_2917_; size_t v_i_boxed_2918_; lean_object* v_res_2919_; 
v___x_34550__boxed_2916_ = lean_unbox(v___x_2904_);
v_sz_boxed_2917_ = lean_unbox_usize(v_sz_2906_);
lean_dec(v_sz_2906_);
v_i_boxed_2918_ = lean_unbox_usize(v_i_2907_);
lean_dec(v_i_2907_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_34550__boxed_2916_, v_as_2905_, v_sz_boxed_2917_, v_i_boxed_2918_, v_b_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
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
uint8_t v___x_34902__boxed_2953_; size_t v_sz_boxed_2954_; size_t v___x_34904__boxed_2955_; lean_object* v_res_2956_; 
v___x_34902__boxed_2953_ = lean_unbox(v___x_2941_);
v_sz_boxed_2954_ = lean_unbox_usize(v_sz_2943_);
lean_dec(v_sz_2943_);
v___x_34904__boxed_2955_ = lean_unbox_usize(v___x_2944_);
lean_dec(v___x_2944_);
v_res_2956_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_34902__boxed_2953_, v___x_2942_, v_sz_boxed_2954_, v___x_34904__boxed_2955_, v___x_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
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
lean_dec_ref(v_a_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2983_, v___y_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_2987_, v_x_2988_, v___y_2989_, v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_x_2988_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_2992_, lean_object* v_ref_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2993_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_ref_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3002_, v_ref_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3012_, lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3022_, lean_object* v_x_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3022_, v_x_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3032_, v___y_3036_, v___y_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object* v_00_u03b1_3050_, lean_object* v_00_u03b2_3051_, lean_object* v_00_u03c3_3052_, lean_object* v_ext_3053_, lean_object* v_b_3054_, uint8_t v_kind_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_3053_, v_b_3054_, v_kind_3055_, v___y_3059_, v___y_3060_, v___y_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object* v_00_u03b1_3064_, lean_object* v_00_u03b2_3065_, lean_object* v_00_u03c3_3066_, lean_object* v_ext_3067_, lean_object* v_b_3068_, lean_object* v_kind_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
uint8_t v_kind_boxed_3077_; lean_object* v_res_3078_; 
v_kind_boxed_3077_ = lean_unbox(v_kind_3069_);
v_res_3078_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_3064_, v_00_u03b2_3065_, v_00_u03c3_3066_, v_ext_3067_, v_b_3068_, v_kind_boxed_3077_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3079_, lean_object* v_msg_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3089_, lean_object* v_msg_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3089_, v_msg_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3099_, v___y_3103_, v___y_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
uint64_t v_h_boxed_3116_; lean_object* v_res_3117_; 
v_h_boxed_3116_ = lean_unbox_uint64(v_h_3108_);
lean_dec_ref(v_h_3108_);
v_res_3117_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3116_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3118_, lean_object* v_msg_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3118_, v_msg_3119_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3128_, lean_object* v_msg_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3128_, v_msg_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3138_, lean_object* v_as_x27_3139_, lean_object* v_b_3140_, lean_object* v_a_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3139_, v_b_3140_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3150_, lean_object* v_as_x27_3151_, lean_object* v_b_3152_, lean_object* v_a_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3150_, v_as_x27_3151_, v_b_3152_, v_a_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v_as_x27_3151_);
lean_dec(v_as_3150_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3162_, lean_object* v_ref_3163_, lean_object* v_msg_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3163_, v_msg_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_ref_3174_, lean_object* v_msg_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3173_, v_ref_3174_, v_msg_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v_ref_3174_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3184_, lean_object* v_t_3185_, uint64_t v_k_3186_, lean_object* v_fallback_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3185_, v_k_3186_, v_fallback_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3189_, lean_object* v_t_3190_, lean_object* v_k_3191_, lean_object* v_fallback_3192_){
_start:
{
uint64_t v_k_boxed_3193_; lean_object* v_res_3194_; 
v_k_boxed_3193_ = lean_unbox_uint64(v_k_3191_);
lean_dec_ref(v_k_3191_);
v_res_3194_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3189_, v_t_3190_, v_k_boxed_3193_, v_fallback_3192_);
lean_dec(v_fallback_3192_);
lean_dec(v_t_3190_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3195_, uint64_t v_k_3196_, lean_object* v_v_3197_, lean_object* v_t_3198_, lean_object* v_hl_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3196_, v_v_3197_, v_t_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3201_, lean_object* v_k_3202_, lean_object* v_v_3203_, lean_object* v_t_3204_, lean_object* v_hl_3205_){
_start:
{
uint64_t v_k_boxed_3206_; lean_object* v_res_3207_; 
v_k_boxed_3206_ = lean_unbox_uint64(v_k_3202_);
lean_dec_ref(v_k_3202_);
v_res_3207_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3201_, v_k_boxed_3206_, v_v_3203_, v_t_3204_, v_hl_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_3208_, lean_object* v_macroStack_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_3208_, v_macroStack_3209_, v___y_3214_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_3218_, lean_object* v_macroStack_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3218_, v_macroStack_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object* v_00_u03b2_3228_, uint64_t v_k_3229_, lean_object* v_t_3230_, lean_object* v_h_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3229_, v_t_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object* v_00_u03b2_3233_, lean_object* v_k_3234_, lean_object* v_t_3235_, lean_object* v_h_3236_){
_start:
{
uint64_t v_k_boxed_3237_; lean_object* v_res_3238_; 
v_k_boxed_3237_ = lean_unbox_uint64(v_k_3234_);
lean_dec_ref(v_k_3234_);
v_res_3238_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_3233_, v_k_boxed_3237_, v_t_3235_, v_h_3236_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3239_, lean_object* v_m_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3240_, v_a_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3243_, lean_object* v_m_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3243_, v_m_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_m_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object* v_00_u03b2_3247_, lean_object* v_x_3248_, lean_object* v_x_3249_){
_start:
{
uint8_t v___x_3250_; 
v___x_3250_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_3248_, v_x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object* v_00_u03b2_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_){
_start:
{
uint8_t v_res_3254_; lean_object* v_r_3255_; 
v_res_3254_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_3251_, v_x_3252_, v_x_3253_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v_x_3252_);
v_r_3255_ = lean_box(v_res_3254_);
return v_r_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object* v_00_u03b2_3256_, lean_object* v_a_3257_, lean_object* v_x_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_3257_, v_x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_a_3261_, lean_object* v_x_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_3260_, v_a_3261_, v_x_3262_);
lean_dec(v_x_3262_);
lean_dec(v_a_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object* v_00_u03b2_3264_, lean_object* v_x_3265_, size_t v_x_3266_, lean_object* v_x_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_3265_, v_x_3266_, v_x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
size_t v_x_35266__boxed_3273_; uint8_t v_res_3274_; lean_object* v_r_3275_; 
v_x_35266__boxed_3273_ = lean_unbox_usize(v_x_3271_);
lean_dec(v_x_3271_);
v_res_3274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_3269_, v_x_3270_, v_x_35266__boxed_3273_, v_x_3272_);
lean_dec_ref(v_x_3272_);
lean_dec_ref(v_x_3270_);
v_r_3275_ = lean_box(v_res_3274_);
return v_r_3275_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object* v_00_u03b2_3276_, lean_object* v_keys_3277_, lean_object* v_vals_3278_, lean_object* v_heq_3279_, lean_object* v_i_3280_, lean_object* v_k_3281_){
_start:
{
uint8_t v___x_3282_; 
v___x_3282_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_3277_, v_i_3280_, v_k_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object* v_00_u03b2_3283_, lean_object* v_keys_3284_, lean_object* v_vals_3285_, lean_object* v_heq_3286_, lean_object* v_i_3287_, lean_object* v_k_3288_){
_start:
{
uint8_t v_res_3289_; lean_object* v_r_3290_; 
v_res_3289_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_3283_, v_keys_3284_, v_vals_3285_, v_heq_3286_, v_i_3287_, v_k_3288_);
lean_dec_ref(v_k_3288_);
lean_dec_ref(v_vals_3285_);
lean_dec_ref(v_keys_3284_);
v_r_3290_ = lean_box(v_res_3289_);
return v_r_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3308_, lean_object* v_x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3308_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3318_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; uint64_t v_javascriptHash_3321_; lean_object* v_props_3322_; lean_object* v___x_3323_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v_javascriptHash_3321_ = lean_ctor_get_uint64(v_a_3320_, sizeof(void*)*2);
v_props_3322_ = lean_ctor_get(v_a_3320_, 1);
lean_inc_ref(v_props_3322_);
lean_dec(v_a_3320_);
v___x_3323_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3321_, v_props_3322_, v_x_3309_, v___y_3314_, v___y_3315_);
return v___x_3323_;
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v_x_3309_);
v_a_3324_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3319_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3319_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec(v_x_3309_);
v_a_3332_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3317_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3317_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3340_, v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3350_);
v___x_3355_ = l_Lean_Syntax_isOfKind(v_x_3350_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec(v_x_3350_);
v___x_3356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3356_;
}
else
{
lean_object* v___x_3357_; lean_object* v_s_3358_; lean_object* v___f_3359_; lean_object* v___x_3360_; 
v___x_3357_ = lean_unsigned_to_nat(1u);
v_s_3358_ = l_Lean_Syntax_getArg(v_x_3350_, v___x_3357_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3359_, 0, v_s_3358_);
lean_closure_set(v___f_3359_, 1, v_x_3350_);
v___x_3360_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3359_, v_a_3351_, v_a_3352_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Widget_elabWidgetCmd(v_x_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3365_;
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
