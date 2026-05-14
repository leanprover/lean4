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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1;
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
lean_dec_ref(v___x_325_);
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
v___x_582_ = lean_st_ref_set(v___y_563_, v___x_581_);
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
v___x_659_ = lean_nat_add(v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
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
lean_ctor_set(v___x_639_, 3, v___y_656_);
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
lean_ctor_set(v_reuseFailAlloc_664_, 3, v___y_656_);
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
v___y_656_ = v___x_671_;
v___y_657_ = v___x_672_;
v___y_658_ = v_size_673_;
goto v___jp_655_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___y_656_ = v___x_671_;
v___y_657_ = v___x_672_;
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
v___x_835_ = lean_nat_add(v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
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
lean_ctor_set(v___x_815_, 3, v___y_832_);
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
lean_ctor_set(v_reuseFailAlloc_840_, 3, v___y_832_);
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
v___y_832_ = v___x_846_;
v___y_833_ = v___x_847_;
v___y_834_ = v_size_848_;
goto v___jp_831_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___y_832_ = v___x_846_;
v___y_833_ = v___x_847_;
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
v___x_976_ = lean_nat_add(v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec(v___y_974_);
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
lean_ctor_set(v___x_980_, 3, v___y_973_);
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
lean_ctor_set(v_reuseFailAlloc_984_, 3, v___y_973_);
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
v___y_973_ = v___x_997_;
v___y_974_ = v___x_998_;
v___y_975_ = v_size_999_;
goto v___jp_972_;
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___y_973_ = v___x_997_;
v___y_974_ = v___x_998_;
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
lean_object* v___x_1295_; lean_object* v_env_1296_; lean_object* v_nextMacroScope_1297_; lean_object* v_ngen_1298_; lean_object* v_auxDeclNGen_1299_; lean_object* v_traceState_1300_; lean_object* v_messages_1301_; lean_object* v_infoState_1302_; lean_object* v_snapshotTasks_1303_; lean_object* v_newDecls_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1334_; 
v___x_1295_ = lean_st_ref_take(v___y_1293_);
v_env_1296_ = lean_ctor_get(v___x_1295_, 0);
v_nextMacroScope_1297_ = lean_ctor_get(v___x_1295_, 1);
v_ngen_1298_ = lean_ctor_get(v___x_1295_, 2);
v_auxDeclNGen_1299_ = lean_ctor_get(v___x_1295_, 3);
v_traceState_1300_ = lean_ctor_get(v___x_1295_, 4);
v_messages_1301_ = lean_ctor_get(v___x_1295_, 6);
v_infoState_1302_ = lean_ctor_get(v___x_1295_, 7);
v_snapshotTasks_1303_ = lean_ctor_get(v___x_1295_, 8);
v_newDecls_1304_ = lean_ctor_get(v___x_1295_, 9);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1295_, 5);
lean_dec(v_unused_1335_);
v___x_1306_ = v___x_1295_;
v_isShared_1307_ = v_isSharedCheck_1334_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_newDecls_1304_);
lean_inc(v_snapshotTasks_1303_);
lean_inc(v_infoState_1302_);
lean_inc(v_messages_1301_);
lean_inc(v_traceState_1300_);
lean_inc(v_auxDeclNGen_1299_);
lean_inc(v_ngen_1298_);
lean_inc(v_nextMacroScope_1297_);
lean_inc(v_env_1296_);
lean_dec(v___x_1295_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1334_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1308_ = lean_box_uint64(v_h_1291_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1309_, 0, v___x_1308_);
v___x_1310_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1311_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1310_, v_env_1296_, v___f_1309_);
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
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_nextMacroScope_1297_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_ngen_1298_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_auxDeclNGen_1299_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_traceState_1300_);
lean_ctor_set(v_reuseFailAlloc_1333_, 5, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1333_, 6, v_messages_1301_);
lean_ctor_set(v_reuseFailAlloc_1333_, 7, v_infoState_1302_);
lean_ctor_set(v_reuseFailAlloc_1333_, 8, v_snapshotTasks_1303_);
lean_ctor_set(v_reuseFailAlloc_1333_, 9, v_newDecls_1304_);
v___x_1314_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_mctx_1317_; lean_object* v_zetaDeltaFVarIds_1318_; lean_object* v_postponed_1319_; lean_object* v_diag_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1331_; 
v___x_1315_ = lean_st_ref_set(v___y_1293_, v___x_1314_);
v___x_1316_ = lean_st_ref_take(v___y_1292_);
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
v___x_1327_ = lean_st_ref_set(v___y_1292_, v___x_1326_);
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
v___x_1412_ = lean_nat_add(v___y_1409_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___y_1409_);
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
lean_ctor_set(v___x_1392_, 3, v___y_1410_);
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
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v___y_1410_);
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
v___y_1409_ = v___x_1424_;
v___y_1410_ = v___x_1423_;
v___y_1411_ = v_size_1425_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___y_1409_ = v___x_1424_;
v___y_1410_ = v___x_1423_;
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
v___x_1551_ = lean_nat_add(v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec(v___y_1549_);
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
lean_ctor_set(v___x_1531_, 3, v___y_1548_);
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
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v___y_1548_);
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
v___y_1548_ = v___x_1563_;
v___y_1549_ = v___x_1564_;
v___y_1550_ = v_size_1565_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
v___y_1548_ = v___x_1563_;
v___y_1549_ = v___x_1564_;
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
lean_object* v___x_1672_; lean_object* v_env_1673_; lean_object* v_nextMacroScope_1674_; lean_object* v_ngen_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_traceState_1677_; lean_object* v_messages_1678_; lean_object* v_infoState_1679_; lean_object* v_snapshotTasks_1680_; lean_object* v_newDecls_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1710_; 
v___x_1672_ = lean_st_ref_take(v___y_1670_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
v_nextMacroScope_1674_ = lean_ctor_get(v___x_1672_, 1);
v_ngen_1675_ = lean_ctor_get(v___x_1672_, 2);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1672_, 3);
v_traceState_1677_ = lean_ctor_get(v___x_1672_, 4);
v_messages_1678_ = lean_ctor_get(v___x_1672_, 6);
v_infoState_1679_ = lean_ctor_get(v___x_1672_, 7);
v_snapshotTasks_1680_ = lean_ctor_get(v___x_1672_, 8);
v_newDecls_1681_ = lean_ctor_get(v___x_1672_, 9);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1672_, 5);
lean_dec(v_unused_1711_);
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1710_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_newDecls_1681_);
lean_inc(v_snapshotTasks_1680_);
lean_inc(v_infoState_1679_);
lean_inc(v_messages_1678_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_ngen_1675_);
lean_inc(v_nextMacroScope_1674_);
lean_inc(v_env_1673_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1710_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___f_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1685_, 0, v_wi_1668_);
v___x_1686_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_1687_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_1686_, v_env_1673_, v___f_1685_);
v___x_1688_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 5, v___x_1688_);
lean_ctor_set(v___x_1683_, 0, v___x_1687_);
v___x_1690_ = v___x_1683_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_nextMacroScope_1674_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_ngen_1675_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_traceState_1677_);
lean_ctor_set(v_reuseFailAlloc_1709_, 5, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1709_, 6, v_messages_1678_);
lean_ctor_set(v_reuseFailAlloc_1709_, 7, v_infoState_1679_);
lean_ctor_set(v_reuseFailAlloc_1709_, 8, v_snapshotTasks_1680_);
lean_ctor_set(v_reuseFailAlloc_1709_, 9, v_newDecls_1681_);
v___x_1690_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_mctx_1693_; lean_object* v_zetaDeltaFVarIds_1694_; lean_object* v_postponed_1695_; lean_object* v_diag_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1707_; 
v___x_1691_ = lean_st_ref_set(v___y_1670_, v___x_1690_);
v___x_1692_ = lean_st_ref_take(v___y_1669_);
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
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_mctx_1693_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_zetaDeltaFVarIds_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_postponed_1695_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_diag_1696_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_st_ref_set(v___y_1669_, v___x_1702_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
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
lean_object* v_currNamespace_1724_; lean_object* v___x_1725_; lean_object* v_env_1726_; lean_object* v_nextMacroScope_1727_; lean_object* v_ngen_1728_; lean_object* v_auxDeclNGen_1729_; lean_object* v_traceState_1730_; lean_object* v_messages_1731_; lean_object* v_infoState_1732_; lean_object* v_snapshotTasks_1733_; lean_object* v_newDecls_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1761_; 
v_currNamespace_1724_ = lean_ctor_get(v___y_1721_, 6);
v___x_1725_ = lean_st_ref_take(v___y_1722_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
v_nextMacroScope_1727_ = lean_ctor_get(v___x_1725_, 1);
v_ngen_1728_ = lean_ctor_get(v___x_1725_, 2);
v_auxDeclNGen_1729_ = lean_ctor_get(v___x_1725_, 3);
v_traceState_1730_ = lean_ctor_get(v___x_1725_, 4);
v_messages_1731_ = lean_ctor_get(v___x_1725_, 6);
v_infoState_1732_ = lean_ctor_get(v___x_1725_, 7);
v_snapshotTasks_1733_ = lean_ctor_get(v___x_1725_, 8);
v_newDecls_1734_ = lean_ctor_get(v___x_1725_, 9);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1725_, 5);
lean_dec(v_unused_1762_);
v___x_1736_ = v___x_1725_;
v_isShared_1737_ = v_isSharedCheck_1761_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_newDecls_1734_);
lean_inc(v_snapshotTasks_1733_);
lean_inc(v_infoState_1732_);
lean_inc(v_messages_1731_);
lean_inc(v_traceState_1730_);
lean_inc(v_auxDeclNGen_1729_);
lean_inc(v_ngen_1728_);
lean_inc(v_nextMacroScope_1727_);
lean_inc(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1761_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_inc(v_currNamespace_1724_);
v___x_1738_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1726_, v_ext_1717_, v_b_1718_, v_kind_1719_, v_currNamespace_1724_);
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
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_nextMacroScope_1727_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_ngen_1728_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_auxDeclNGen_1729_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_traceState_1730_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v_messages_1731_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_infoState_1732_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_snapshotTasks_1733_);
lean_ctor_set(v_reuseFailAlloc_1760_, 9, v_newDecls_1734_);
v___x_1741_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_mctx_1744_; lean_object* v_zetaDeltaFVarIds_1745_; lean_object* v_postponed_1746_; lean_object* v_diag_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1758_; 
v___x_1742_ = lean_st_ref_set(v___y_1722_, v___x_1741_);
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
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_mctx_1744_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_zetaDeltaFVarIds_1745_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_postponed_1746_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_diag_1747_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_st_ref_set(v___y_1720_, v___x_1753_);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
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
lean_object* v___x_1848_; lean_object* v_env_1849_; lean_object* v___x_1850_; lean_object* v_mctx_1851_; lean_object* v_lctx_1852_; lean_object* v_options_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1848_ = lean_st_ref_get(v___y_1846_);
v_env_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref(v_env_1849_);
lean_dec(v___x_1848_);
v___x_1850_ = lean_st_ref_get(v___y_1844_);
v_mctx_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc_ref(v_mctx_1851_);
lean_dec(v___x_1850_);
v_lctx_1852_ = lean_ctor_get(v___y_1843_, 2);
v_options_1853_ = lean_ctor_get(v___y_1845_, 2);
lean_inc_ref(v_options_1853_);
lean_inc_ref(v_lctx_1852_);
v___x_1854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1854_, 0, v_env_1849_);
lean_ctor_set(v___x_1854_, 1, v_mctx_1851_);
lean_ctor_set(v___x_1854_, 2, v_lctx_1852_);
lean_ctor_set(v___x_1854_, 3, v_options_1853_);
v___x_1855_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v_msgData_1842_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(lean_object* v_msgData_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1863_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1864_; double v___x_1865_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_float_of_nat(v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(lean_object* v_cls_1868_, lean_object* v_msg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_ref_1875_; lean_object* v___x_1876_; lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1922_; 
v_ref_1875_ = lean_ctor_get(v___y_1872_, 5);
v___x_1876_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1922_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1922_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v_traceState_1882_; lean_object* v_env_1883_; lean_object* v_nextMacroScope_1884_; lean_object* v_ngen_1885_; lean_object* v_auxDeclNGen_1886_; lean_object* v_cache_1887_; lean_object* v_messages_1888_; lean_object* v_infoState_1889_; lean_object* v_snapshotTasks_1890_; lean_object* v_newDecls_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1921_; 
v___x_1881_ = lean_st_ref_take(v___y_1873_);
v_traceState_1882_ = lean_ctor_get(v___x_1881_, 4);
v_env_1883_ = lean_ctor_get(v___x_1881_, 0);
v_nextMacroScope_1884_ = lean_ctor_get(v___x_1881_, 1);
v_ngen_1885_ = lean_ctor_get(v___x_1881_, 2);
v_auxDeclNGen_1886_ = lean_ctor_get(v___x_1881_, 3);
v_cache_1887_ = lean_ctor_get(v___x_1881_, 5);
v_messages_1888_ = lean_ctor_get(v___x_1881_, 6);
v_infoState_1889_ = lean_ctor_get(v___x_1881_, 7);
v_snapshotTasks_1890_ = lean_ctor_get(v___x_1881_, 8);
v_newDecls_1891_ = lean_ctor_get(v___x_1881_, 9);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1893_ = v___x_1881_;
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_newDecls_1891_);
lean_inc(v_snapshotTasks_1890_);
lean_inc(v_infoState_1889_);
lean_inc(v_messages_1888_);
lean_inc(v_cache_1887_);
lean_inc(v_traceState_1882_);
lean_inc(v_auxDeclNGen_1886_);
lean_inc(v_ngen_1885_);
lean_inc(v_nextMacroScope_1884_);
lean_inc(v_env_1883_);
lean_dec(v___x_1881_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
uint64_t v_tid_1895_; lean_object* v_traces_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1920_; 
v_tid_1895_ = lean_ctor_get_uint64(v_traceState_1882_, sizeof(void*)*1);
v_traces_1896_ = lean_ctor_get(v_traceState_1882_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_traceState_1882_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1898_ = v_traceState_1882_;
v_isShared_1899_ = v_isSharedCheck_1920_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_traces_1896_);
lean_dec(v_traceState_1882_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1920_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; double v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
v___x_1902_ = 0;
v___x_1903_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_1904_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1904_, 0, v_cls_1868_);
lean_ctor_set(v___x_1904_, 1, v___x_1900_);
lean_ctor_set(v___x_1904_, 2, v___x_1903_);
lean_ctor_set_float(v___x_1904_, sizeof(void*)*3, v___x_1901_);
lean_ctor_set_float(v___x_1904_, sizeof(void*)*3 + 8, v___x_1901_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*3 + 16, v___x_1902_);
v___x_1905_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1));
v___x_1906_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v_a_1877_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_inc(v_ref_1875_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_ref_1875_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_PersistentArray_push___redArg(v_traces_1896_, v___x_1907_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1908_);
v___x_1910_ = v___x_1898_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1908_);
lean_ctor_set_uint64(v_reuseFailAlloc_1919_, sizeof(void*)*1, v_tid_1895_);
v___x_1910_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v___x_1910_);
v___x_1912_ = v___x_1893_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_env_1883_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_nextMacroScope_1884_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_ngen_1885_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_auxDeclNGen_1886_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_cache_1887_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_messages_1888_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_infoState_1889_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_snapshotTasks_1890_);
lean_ctor_set(v_reuseFailAlloc_1918_, 9, v_newDecls_1891_);
v___x_1912_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1913_ = lean_st_ref_set(v___y_1873_, v___x_1912_);
v___x_1914_ = lean_box(0);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1914_);
v___x_1916_ = v___x_1879_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
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
lean_object* v_options_1944_; uint8_t v_hasTrace_1945_; 
v_options_1944_ = lean_ctor_get(v___y_1939_, 2);
v_hasTrace_1945_ = lean_ctor_get_uint8(v_options_1944_, sizeof(void*)*1);
if (v_hasTrace_1945_ == 0)
{
lean_object* v_tail_1946_; 
v_tail_1946_ = lean_ctor_get(v_as_1934_, 1);
lean_inc(v_tail_1946_);
lean_dec_ref(v_as_1934_);
v_as_1934_ = v_tail_1946_;
goto _start;
}
else
{
lean_object* v_head_1948_; lean_object* v_tail_1949_; lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v_inheritedTraceOptions_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v_head_1948_ = lean_ctor_get(v_as_1934_, 0);
lean_inc(v_head_1948_);
v_tail_1949_ = lean_ctor_get(v_as_1934_, 1);
lean_inc(v_tail_1949_);
lean_dec_ref(v_as_1934_);
v_fst_1950_ = lean_ctor_get(v_head_1948_, 0);
lean_inc_n(v_fst_1950_, 2);
v_snd_1951_ = lean_ctor_get(v_head_1948_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_head_1948_);
v_inheritedTraceOptions_1952_ = lean_ctor_get(v___y_1939_, 13);
v___x_1953_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_1954_ = l_Lean_Name_append(v___x_1953_, v_fst_1950_);
v___x_1955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1952_, v_options_1944_, v___x_1954_);
lean_dec(v___x_1954_);
if (v___x_1955_ == 0)
{
lean_dec(v_snd_1951_);
lean_dec(v_fst_1950_);
v_as_1934_ = v_tail_1949_;
goto _start;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_snd_1951_);
v___x_1958_ = l_Lean_MessageData_ofFormat(v___x_1957_);
v___x_1959_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_1950_, v___x_1958_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_dec_ref(v___x_1959_);
v_as_1934_ = v_tail_1949_;
goto _start;
}
else
{
lean_dec(v_tail_1949_);
return v___x_1959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(lean_object* v_as_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(lean_object* v_env_1970_, lean_object* v_currNamespace_1971_, lean_object* v_openDecls_1972_, lean_object* v_n_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = l_Lean_ResolveName_resolveNamespace(v_env_1970_, v_currNamespace_1971_, v_openDecls_1972_, v_n_1973_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___y_1975_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(lean_object* v_env_1978_, lean_object* v_currNamespace_1979_, lean_object* v_openDecls_1980_, lean_object* v_n_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_env_1978_, v_currNamespace_1979_, v_openDecls_1980_, v_n_1981_, v___y_1982_, v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(lean_object* v_opts_1985_, lean_object* v_opt_1986_){
_start:
{
lean_object* v_name_1987_; lean_object* v_defValue_1988_; lean_object* v_map_1989_; lean_object* v___x_1990_; 
v_name_1987_ = lean_ctor_get(v_opt_1986_, 0);
v_defValue_1988_ = lean_ctor_get(v_opt_1986_, 1);
v_map_1989_ = lean_ctor_get(v_opts_1985_, 0);
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1989_, v_name_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_unbox(v_defValue_1988_);
return v___x_1991_;
}
else
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_val_1992_);
lean_dec_ref(v___x_1990_);
if (lean_obj_tag(v_val_1992_) == 1)
{
uint8_t v_v_1993_; 
v_v_1993_ = lean_ctor_get_uint8(v_val_1992_, 0);
lean_dec_ref(v_val_1992_);
return v_v_1993_;
}
else
{
uint8_t v___x_1994_; 
lean_dec(v_val_1992_);
v___x_1994_ = lean_unbox(v_defValue_1988_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(lean_object* v_opts_1995_, lean_object* v_opt_1996_){
_start:
{
uint8_t v_res_1997_; lean_object* v_r_1998_; 
v_res_1997_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_1995_, v_opt_1996_);
lean_dec_ref(v_opt_1996_);
lean_dec_ref(v_opts_1995_);
v_r_1998_ = lean_box(v_res_1997_);
return v_r_1998_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_box(1);
v___x_2000_ = l_Lean_MessageData_ofFormat(v___x_1999_);
return v___x_2000_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2));
v___x_2005_ = l_Lean_MessageData_ofFormat(v___x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(lean_object* v_x_2006_, lean_object* v_x_2007_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 0)
{
return v_x_2006_;
}
else
{
lean_object* v_head_2008_; lean_object* v_tail_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2031_; 
v_head_2008_ = lean_ctor_get(v_x_2007_, 0);
v_tail_2009_ = lean_ctor_get(v_x_2007_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_x_2007_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2011_ = v_x_2007_;
v_isShared_2012_ = v_isSharedCheck_2031_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_tail_2009_);
lean_inc(v_head_2008_);
lean_dec(v_x_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2031_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_before_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2029_; 
v_before_2013_ = lean_ctor_get(v_head_2008_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_head_2008_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_head_2008_, 1);
lean_dec(v_unused_2030_);
v___x_2015_ = v_head_2008_;
v_isShared_2016_ = v_isSharedCheck_2029_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_before_2013_);
lean_dec(v_head_2008_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2029_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 7);
lean_ctor_set(v___x_2015_, 1, v___x_2017_);
lean_ctor_set(v___x_2015_, 0, v_x_2006_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_x_2006_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 7);
lean_ctor_set(v___x_2011_, 1, v___x_2020_);
lean_ctor_set(v___x_2011_, 0, v___x_2019_);
v___x_2022_ = v___x_2011_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = l_Lean_MessageData_ofSyntax(v_before_2013_);
v___x_2024_ = l_Lean_indentD(v___x_2023_);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2022_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v_x_2006_ = v___x_2025_;
v_x_2007_ = v_tail_2009_;
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
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1));
v___x_2036_ = l_Lean_MessageData_ofFormat(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(lean_object* v_msgData_2037_, lean_object* v_macroStack_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_options_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_options_2041_ = lean_ctor_get(v___y_2039_, 2);
v___x_2042_ = l_Lean_Elab_pp_macroStack;
v___x_2043_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_options_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v_macroStack_2038_);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_msgData_2037_);
return v___x_2044_;
}
else
{
if (lean_obj_tag(v_macroStack_2038_) == 0)
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_msgData_2037_);
return v___x_2045_;
}
else
{
lean_object* v_head_2046_; lean_object* v_after_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2062_; 
v_head_2046_ = lean_ctor_get(v_macroStack_2038_, 0);
lean_inc(v_head_2046_);
v_after_2047_ = lean_ctor_get(v_head_2046_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_head_2046_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v_head_2046_, 0);
lean_dec(v_unused_2063_);
v___x_2049_ = v_head_2046_;
v_isShared_2050_ = v_isSharedCheck_2062_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_after_2047_);
lean_dec(v_head_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2062_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 7);
lean_ctor_set(v___x_2049_, 1, v___x_2051_);
lean_ctor_set(v___x_2049_, 0, v_msgData_2037_);
v___x_2053_ = v___x_2049_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_msgData_2037_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_msgData_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2054_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = l_Lean_MessageData_ofSyntax(v_after_2047_);
v___x_2057_ = l_Lean_indentD(v___x_2056_);
v_msgData_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2058_, 0, v___x_2055_);
lean_ctor_set(v_msgData_2058_, 1, v___x_2057_);
v___x_2059_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_2058_, v_macroStack_2038_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(lean_object* v_msgData_2064_, lean_object* v_macroStack_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_2064_, v_macroStack_2065_, v___y_2066_);
lean_dec_ref(v___y_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_ref_2077_; lean_object* v___x_2078_; lean_object* v_a_2079_; lean_object* v_macroStack_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_ref_2077_ = lean_ctor_get(v___y_2074_, 5);
v___x_2078_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_2069_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
v_macroStack_2080_ = lean_ctor_get(v___y_2070_, 1);
v___x_2081_ = l_Lean_Elab_getBetterRef(v_ref_2077_, v_macroStack_2080_);
lean_inc(v_macroStack_2080_);
v___x_2082_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_2079_, v_macroStack_2080_, v___y_2074_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2081_);
lean_ctor_set(v___x_2087_, 1, v_a_2083_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 1);
lean_ctor_set(v___x_2085_, 0, v___x_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(lean_object* v_ref_2101_, lean_object* v_msg_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_fileName_2110_; lean_object* v_fileMap_2111_; lean_object* v_options_2112_; lean_object* v_currRecDepth_2113_; lean_object* v_maxRecDepth_2114_; lean_object* v_ref_2115_; lean_object* v_currNamespace_2116_; lean_object* v_openDecls_2117_; lean_object* v_initHeartbeats_2118_; lean_object* v_maxHeartbeats_2119_; lean_object* v_quotContext_2120_; lean_object* v_currMacroScope_2121_; uint8_t v_diag_2122_; lean_object* v_cancelTk_x3f_2123_; uint8_t v_suppressElabErrors_2124_; lean_object* v_inheritedTraceOptions_2125_; lean_object* v_ref_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_fileName_2110_ = lean_ctor_get(v___y_2107_, 0);
v_fileMap_2111_ = lean_ctor_get(v___y_2107_, 1);
v_options_2112_ = lean_ctor_get(v___y_2107_, 2);
v_currRecDepth_2113_ = lean_ctor_get(v___y_2107_, 3);
v_maxRecDepth_2114_ = lean_ctor_get(v___y_2107_, 4);
v_ref_2115_ = lean_ctor_get(v___y_2107_, 5);
v_currNamespace_2116_ = lean_ctor_get(v___y_2107_, 6);
v_openDecls_2117_ = lean_ctor_get(v___y_2107_, 7);
v_initHeartbeats_2118_ = lean_ctor_get(v___y_2107_, 8);
v_maxHeartbeats_2119_ = lean_ctor_get(v___y_2107_, 9);
v_quotContext_2120_ = lean_ctor_get(v___y_2107_, 10);
v_currMacroScope_2121_ = lean_ctor_get(v___y_2107_, 11);
v_diag_2122_ = lean_ctor_get_uint8(v___y_2107_, sizeof(void*)*14);
v_cancelTk_x3f_2123_ = lean_ctor_get(v___y_2107_, 12);
v_suppressElabErrors_2124_ = lean_ctor_get_uint8(v___y_2107_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2125_ = lean_ctor_get(v___y_2107_, 13);
v_ref_2126_ = l_Lean_replaceRef(v_ref_2101_, v_ref_2115_);
lean_inc_ref(v_inheritedTraceOptions_2125_);
lean_inc(v_cancelTk_x3f_2123_);
lean_inc(v_currMacroScope_2121_);
lean_inc(v_quotContext_2120_);
lean_inc(v_maxHeartbeats_2119_);
lean_inc(v_initHeartbeats_2118_);
lean_inc(v_openDecls_2117_);
lean_inc(v_currNamespace_2116_);
lean_inc(v_maxRecDepth_2114_);
lean_inc(v_currRecDepth_2113_);
lean_inc_ref(v_options_2112_);
lean_inc_ref(v_fileMap_2111_);
lean_inc_ref(v_fileName_2110_);
v___x_2127_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2127_, 0, v_fileName_2110_);
lean_ctor_set(v___x_2127_, 1, v_fileMap_2111_);
lean_ctor_set(v___x_2127_, 2, v_options_2112_);
lean_ctor_set(v___x_2127_, 3, v_currRecDepth_2113_);
lean_ctor_set(v___x_2127_, 4, v_maxRecDepth_2114_);
lean_ctor_set(v___x_2127_, 5, v_ref_2126_);
lean_ctor_set(v___x_2127_, 6, v_currNamespace_2116_);
lean_ctor_set(v___x_2127_, 7, v_openDecls_2117_);
lean_ctor_set(v___x_2127_, 8, v_initHeartbeats_2118_);
lean_ctor_set(v___x_2127_, 9, v_maxHeartbeats_2119_);
lean_ctor_set(v___x_2127_, 10, v_quotContext_2120_);
lean_ctor_set(v___x_2127_, 11, v_currMacroScope_2121_);
lean_ctor_set(v___x_2127_, 12, v_cancelTk_x3f_2123_);
lean_ctor_set(v___x_2127_, 13, v_inheritedTraceOptions_2125_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*14, v_diag_2122_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*14 + 1, v_suppressElabErrors_2124_);
v___x_2128_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___x_2127_, v___y_2108_);
lean_dec_ref(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2129_, lean_object* v_msg_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_2129_, v_msg_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v_ref_2129_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(lean_object* v_env_2139_, lean_object* v_options_2140_, lean_object* v_currNamespace_2141_, lean_object* v_openDecls_2142_, lean_object* v_n_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = l_Lean_ResolveName_resolveGlobalName(v_env_2139_, v_options_2140_, v_currNamespace_2141_, v_openDecls_2142_, v_n_2143_);
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(lean_object* v_env_2148_, lean_object* v_options_2149_, lean_object* v_currNamespace_2150_, lean_object* v_openDecls_2151_, lean_object* v_n_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_2148_, v_options_2149_, v_currNamespace_2150_, v_openDecls_2151_, v_n_2152_, v___y_2153_, v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_options_2149_);
return v_res_2155_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(lean_object* v_keys_2156_, lean_object* v_i_2157_, lean_object* v_k_2158_){
_start:
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = lean_array_get_size(v_keys_2156_);
v___x_2160_ = lean_nat_dec_lt(v_i_2157_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_dec(v_i_2157_);
return v___x_2160_;
}
else
{
lean_object* v_k_x27_2161_; uint8_t v___x_2162_; 
v_k_x27_2161_ = lean_array_fget_borrowed(v_keys_2156_, v_i_2157_);
v___x_2162_ = l_Lean_instBEqExtraModUse_beq(v_k_2158_, v_k_x27_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = lean_nat_add(v_i_2157_, v___x_2163_);
lean_dec(v_i_2157_);
v_i_2157_ = v___x_2164_;
goto _start;
}
else
{
lean_dec(v_i_2157_);
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(lean_object* v_keys_2166_, lean_object* v_i_2167_, lean_object* v_k_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_2166_, v_i_2167_, v_k_2168_);
lean_dec_ref(v_k_2168_);
lean_dec_ref(v_keys_2166_);
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0(void){
_start:
{
size_t v___x_2171_; size_t v___x_2172_; size_t v___x_2173_; 
v___x_2171_ = ((size_t)5ULL);
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = lean_usize_shift_left(v___x_2172_, v___x_2171_);
return v___x_2173_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1(void){
_start:
{
size_t v___x_2174_; size_t v___x_2175_; size_t v___x_2176_; 
v___x_2174_ = ((size_t)1ULL);
v___x_2175_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0);
v___x_2176_ = lean_usize_sub(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(lean_object* v_x_2177_, size_t v_x_2178_, lean_object* v_x_2179_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 0)
{
lean_object* v_es_2180_; lean_object* v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; lean_object* v_j_2185_; lean_object* v___x_2186_; 
v_es_2180_ = lean_ctor_get(v_x_2177_, 0);
v___x_2181_ = lean_box(2);
v___x_2182_ = ((size_t)5ULL);
v___x_2183_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1);
v___x_2184_ = lean_usize_land(v_x_2178_, v___x_2183_);
v_j_2185_ = lean_usize_to_nat(v___x_2184_);
v___x_2186_ = lean_array_get_borrowed(v___x_2181_, v_es_2180_, v_j_2185_);
lean_dec(v_j_2185_);
switch(lean_obj_tag(v___x_2186_))
{
case 0:
{
lean_object* v_key_2187_; uint8_t v___x_2188_; 
v_key_2187_ = lean_ctor_get(v___x_2186_, 0);
v___x_2188_ = l_Lean_instBEqExtraModUse_beq(v_x_2179_, v_key_2187_);
return v___x_2188_;
}
case 1:
{
lean_object* v_node_2189_; size_t v___x_2190_; 
v_node_2189_ = lean_ctor_get(v___x_2186_, 0);
v___x_2190_ = lean_usize_shift_right(v_x_2178_, v___x_2182_);
v_x_2177_ = v_node_2189_;
v_x_2178_ = v___x_2190_;
goto _start;
}
default: 
{
uint8_t v___x_2192_; 
v___x_2192_ = 0;
return v___x_2192_;
}
}
}
else
{
lean_object* v_ks_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_ks_2193_ = lean_ctor_get(v_x_2177_, 0);
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_2193_, v___x_2194_, v_x_2179_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
size_t v_x_33614__boxed_2199_; uint8_t v_res_2200_; lean_object* v_r_2201_; 
v_x_33614__boxed_2199_ = lean_unbox_usize(v_x_2197_);
lean_dec(v_x_2197_);
v_res_2200_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2196_, v_x_33614__boxed_2199_, v_x_2198_);
lean_dec_ref(v_x_2198_);
lean_dec_ref(v_x_2196_);
v_r_2201_ = lean_box(v_res_2200_);
return v_r_2201_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
uint64_t v___x_2204_; size_t v___x_2205_; uint8_t v___x_2206_; 
v___x_2204_ = l_Lean_instHashableExtraModUse_hash(v_x_2203_);
v___x_2205_ = lean_uint64_to_usize(v___x_2204_);
v___x_2206_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_2202_, v___x_2205_, v_x_2203_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
uint8_t v_res_2209_; lean_object* v_r_2210_; 
v_res_2209_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_2207_, v_x_2208_);
lean_dec_ref(v_x_2208_);
lean_dec_ref(v_x_2207_);
v_r_2210_ = lean_box(v_res_2209_);
return v_r_2210_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1));
v___x_2214_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0));
v___x_2215_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2214_, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v_cls_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_cls_2227_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4));
v___x_2228_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1));
v___x_2229_ = l_Lean_Name_append(v___x_2228_, v_cls_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(lean_object* v_mod_2240_, uint8_t v_isMeta_2241_, lean_object* v_hint_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v_env_2251_; uint8_t v_isExporting_2252_; lean_object* v___x_2253_; lean_object* v_env_2254_; lean_object* v___x_2255_; lean_object* v_entry_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2250_ = lean_st_ref_get(v___y_2248_);
v_env_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_env_2251_);
lean_dec(v___x_2250_);
v_isExporting_2252_ = lean_ctor_get_uint8(v_env_2251_, sizeof(void*)*8);
lean_dec_ref(v_env_2251_);
v___x_2253_ = lean_st_ref_get(v___y_2248_);
v_env_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc_ref(v_env_2254_);
lean_dec(v___x_2253_);
v___x_2255_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2);
lean_inc(v_mod_2240_);
v_entry_2256_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2256_, 0, v_mod_2240_);
lean_ctor_set_uint8(v_entry_2256_, sizeof(void*)*1, v_isExporting_2252_);
lean_ctor_set_uint8(v_entry_2256_, sizeof(void*)*1 + 1, v_isMeta_2241_);
v___x_2257_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2258_ = lean_box(1);
v___x_2259_ = lean_box(0);
v___x_2303_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2255_, v___x_2257_, v_env_2254_, v___x_2258_, v___x_2259_);
v___x_2304_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_2303_, v_entry_2256_);
lean_dec(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v_options_2305_; uint8_t v_hasTrace_2306_; 
v_options_2305_ = lean_ctor_get(v___y_2247_, 2);
v_hasTrace_2306_ = lean_ctor_get_uint8(v_options_2305_, sizeof(void*)*1);
if (v_hasTrace_2306_ == 0)
{
lean_dec(v_hint_2242_);
lean_dec(v_mod_2240_);
v___y_2261_ = v___y_2246_;
v___y_2262_ = v___y_2248_;
goto v___jp_2260_;
}
else
{
lean_object* v_inheritedTraceOptions_2307_; lean_object* v_cls_2308_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_inheritedTraceOptions_2307_ = lean_ctor_get(v___y_2247_, 13);
v_cls_2308_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4));
v___x_2328_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
v___x_2329_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2307_, v_options_2305_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec(v_hint_2242_);
lean_dec(v_mod_2240_);
v___y_2261_ = v___y_2246_;
v___y_2262_ = v___y_2248_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2330_; lean_object* v___y_2332_; 
v___x_2330_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
if (v_isExporting_2252_ == 0)
{
lean_object* v___x_2339_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17));
v___y_2332_ = v___x_2339_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18));
v___y_2332_ = v___x_2340_;
goto v___jp_2331_;
}
v___jp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_inc_ref(v___y_2332_);
v___x_2333_ = l_Lean_stringToMessageData(v___y_2332_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2330_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
if (v_isMeta_2241_ == 0)
{
lean_object* v___x_2337_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15));
v___y_2315_ = v___x_2336_;
v___y_2316_ = v___x_2337_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2338_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16));
v___y_2315_ = v___x_2336_;
v___y_2316_ = v___x_2338_;
goto v___jp_2314_;
}
}
}
v___jp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___y_2310_);
lean_ctor_set(v___x_2312_, 1, v___y_2311_);
v___x_2313_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_2308_, v___x_2312_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref(v___x_2313_);
v___y_2261_ = v___y_2246_;
v___y_2262_ = v___y_2248_;
goto v___jp_2260_;
}
else
{
lean_dec_ref(v_entry_2256_);
return v___x_2313_;
}
}
v___jp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
lean_inc_ref(v___y_2316_);
v___x_2317_ = l_Lean_stringToMessageData(v___y_2316_);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___y_2315_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_MessageData_ofName(v_mod_2240_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_Name_isAnonymous(v_hint_2242_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
v___x_2325_ = l_Lean_MessageData_ofName(v_hint_2242_);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___y_2310_ = v___x_2322_;
v___y_2311_ = v___x_2326_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2327_; 
lean_dec(v_hint_2242_);
v___x_2327_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9);
v___y_2310_ = v___x_2322_;
v___y_2311_ = v___x_2327_;
goto v___jp_2309_;
}
}
}
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec_ref(v_entry_2256_);
lean_dec(v_hint_2242_);
lean_dec(v_mod_2240_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
v___jp_2260_:
{
lean_object* v___x_2263_; lean_object* v_toEnvExtension_2264_; lean_object* v_env_2265_; lean_object* v_nextMacroScope_2266_; lean_object* v_ngen_2267_; lean_object* v_auxDeclNGen_2268_; lean_object* v_traceState_2269_; lean_object* v_messages_2270_; lean_object* v_infoState_2271_; lean_object* v_snapshotTasks_2272_; lean_object* v_newDecls_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2301_; 
v___x_2263_ = lean_st_ref_take(v___y_2262_);
v_toEnvExtension_2264_ = lean_ctor_get(v___x_2257_, 0);
v_env_2265_ = lean_ctor_get(v___x_2263_, 0);
v_nextMacroScope_2266_ = lean_ctor_get(v___x_2263_, 1);
v_ngen_2267_ = lean_ctor_get(v___x_2263_, 2);
v_auxDeclNGen_2268_ = lean_ctor_get(v___x_2263_, 3);
v_traceState_2269_ = lean_ctor_get(v___x_2263_, 4);
v_messages_2270_ = lean_ctor_get(v___x_2263_, 6);
v_infoState_2271_ = lean_ctor_get(v___x_2263_, 7);
v_snapshotTasks_2272_ = lean_ctor_get(v___x_2263_, 8);
v_newDecls_2273_ = lean_ctor_get(v___x_2263_, 9);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v___x_2263_, 5);
lean_dec(v_unused_2302_);
v___x_2275_ = v___x_2263_;
v_isShared_2276_ = v_isSharedCheck_2301_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_newDecls_2273_);
lean_inc(v_snapshotTasks_2272_);
lean_inc(v_infoState_2271_);
lean_inc(v_messages_2270_);
lean_inc(v_traceState_2269_);
lean_inc(v_auxDeclNGen_2268_);
lean_inc(v_ngen_2267_);
lean_inc(v_nextMacroScope_2266_);
lean_inc(v_env_2265_);
lean_dec(v___x_2263_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2301_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v_asyncMode_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v_asyncMode_2277_ = lean_ctor_get(v_toEnvExtension_2264_, 2);
v___x_2278_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2257_, v_env_2265_, v_entry_2256_, v_asyncMode_2277_, v___x_2259_);
v___x_2279_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 5, v___x_2279_);
lean_ctor_set(v___x_2275_, 0, v___x_2278_);
v___x_2281_ = v___x_2275_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_nextMacroScope_2266_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_ngen_2267_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_auxDeclNGen_2268_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_traceState_2269_);
lean_ctor_set(v_reuseFailAlloc_2300_, 5, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2300_, 6, v_messages_2270_);
lean_ctor_set(v_reuseFailAlloc_2300_, 7, v_infoState_2271_);
lean_ctor_set(v_reuseFailAlloc_2300_, 8, v_snapshotTasks_2272_);
lean_ctor_set(v_reuseFailAlloc_2300_, 9, v_newDecls_2273_);
v___x_2281_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_mctx_2284_; lean_object* v_zetaDeltaFVarIds_2285_; lean_object* v_postponed_2286_; lean_object* v_diag_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2298_; 
v___x_2282_ = lean_st_ref_set(v___y_2262_, v___x_2281_);
v___x_2283_ = lean_st_ref_take(v___y_2261_);
v_mctx_2284_ = lean_ctor_get(v___x_2283_, 0);
v_zetaDeltaFVarIds_2285_ = lean_ctor_get(v___x_2283_, 2);
v_postponed_2286_ = lean_ctor_get(v___x_2283_, 3);
v_diag_2287_ = lean_ctor_get(v___x_2283_, 4);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v___x_2283_, 1);
lean_dec(v_unused_2299_);
v___x_2289_ = v___x_2283_;
v_isShared_2290_ = v_isSharedCheck_2298_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_diag_2287_);
lean_inc(v_postponed_2286_);
lean_inc(v_zetaDeltaFVarIds_2285_);
lean_inc(v_mctx_2284_);
lean_dec(v___x_2283_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2298_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_obj_once(&l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3, &l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once, _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_mctx_2284_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_zetaDeltaFVarIds_2285_);
lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_postponed_2286_);
lean_ctor_set(v_reuseFailAlloc_2297_, 4, v_diag_2287_);
v___x_2293_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_st_ref_set(v___y_2261_, v___x_2293_);
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2343_, lean_object* v_isMeta_2344_, lean_object* v_hint_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_isMeta_boxed_2353_; lean_object* v_res_2354_; 
v_isMeta_boxed_2353_ = lean_unbox(v_isMeta_2344_);
v_res_2354_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_2343_, v_isMeta_boxed_2353_, v_hint_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(lean_object* v___x_2355_, lean_object* v_declName_2356_, lean_object* v_as_2357_, size_t v_sz_2358_, size_t v_i_2359_, lean_object* v_b_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_usize_dec_lt(v_i_2359_, v_sz_2358_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec(v_declName_2356_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_b_2360_);
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; lean_object* v_modules_2371_; lean_object* v___x_2372_; lean_object* v_a_2373_; lean_object* v___x_2374_; lean_object* v_toImport_2375_; lean_object* v_module_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2370_ = l_Lean_Environment_header(v___x_2355_);
v_modules_2371_ = lean_ctor_get(v___x_2370_, 3);
lean_inc_ref(v_modules_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2373_ = lean_array_uget_borrowed(v_as_2357_, v_i_2359_);
v___x_2374_ = lean_array_get(v___x_2372_, v_modules_2371_, v_a_2373_);
lean_dec_ref(v_modules_2371_);
v_toImport_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc_ref(v_toImport_2375_);
lean_dec(v___x_2374_);
v_module_2376_ = lean_ctor_get(v_toImport_2375_, 0);
lean_inc(v_module_2376_);
lean_dec_ref(v_toImport_2375_);
v___x_2377_ = 0;
lean_inc(v_declName_2356_);
v___x_2378_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2376_, v___x_2377_, v_declName_2356_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; 
lean_dec_ref(v___x_2378_);
v___x_2379_ = lean_box(0);
v___x_2380_ = ((size_t)1ULL);
v___x_2381_ = lean_usize_add(v_i_2359_, v___x_2380_);
v_i_2359_ = v___x_2381_;
v_b_2360_ = v___x_2379_;
goto _start;
}
else
{
lean_dec(v_declName_2356_);
return v___x_2378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2383_, lean_object* v_declName_2384_, lean_object* v_as_2385_, lean_object* v_sz_2386_, lean_object* v_i_2387_, lean_object* v_b_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
size_t v_sz_boxed_2396_; size_t v_i_boxed_2397_; lean_object* v_res_2398_; 
v_sz_boxed_2396_ = lean_unbox_usize(v_sz_2386_);
lean_dec(v_sz_2386_);
v_i_boxed_2397_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_2383_, v_declName_2384_, v_as_2385_, v_sz_boxed_2396_, v_i_boxed_2397_, v_b_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec_ref(v_as_2385_);
lean_dec_ref(v___x_2383_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(lean_object* v_a_2399_, lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2400_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_box(0);
return v___x_2401_;
}
else
{
lean_object* v_key_2402_; lean_object* v_value_2403_; lean_object* v_tail_2404_; uint8_t v___x_2405_; 
v_key_2402_ = lean_ctor_get(v_x_2400_, 0);
v_value_2403_ = lean_ctor_get(v_x_2400_, 1);
v_tail_2404_ = lean_ctor_get(v_x_2400_, 2);
v___x_2405_ = lean_name_eq(v_key_2402_, v_a_2399_);
if (v___x_2405_ == 0)
{
v_x_2400_ = v_tail_2404_;
goto _start;
}
else
{
lean_object* v___x_2407_; 
lean_inc(v_value_2403_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_value_2403_);
return v___x_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(lean_object* v_a_2408_, lean_object* v_x_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2408_, v_x_2409_);
lean_dec(v_x_2409_);
lean_dec(v_a_2408_);
return v_res_2410_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2411_; uint64_t v___x_2412_; 
v___x_2411_ = lean_unsigned_to_nat(1723u);
v___x_2412_ = lean_uint64_of_nat(v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_buckets_2415_; lean_object* v___x_2416_; uint64_t v___y_2418_; 
v_buckets_2415_ = lean_ctor_get(v_m_2413_, 1);
v___x_2416_ = lean_array_get_size(v_buckets_2415_);
if (lean_obj_tag(v_a_2414_) == 0)
{
uint64_t v___x_2432_; 
v___x_2432_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0);
v___y_2418_ = v___x_2432_;
goto v___jp_2417_;
}
else
{
uint64_t v_hash_2433_; 
v_hash_2433_ = lean_ctor_get_uint64(v_a_2414_, sizeof(void*)*2);
v___y_2418_ = v_hash_2433_;
goto v___jp_2417_;
}
v___jp_2417_:
{
uint64_t v___x_2419_; uint64_t v___x_2420_; uint64_t v_fold_2421_; uint64_t v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; size_t v___x_2427_; size_t v___x_2428_; size_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2419_ = 32ULL;
v___x_2420_ = lean_uint64_shift_right(v___y_2418_, v___x_2419_);
v_fold_2421_ = lean_uint64_xor(v___y_2418_, v___x_2420_);
v___x_2422_ = 16ULL;
v___x_2423_ = lean_uint64_shift_right(v_fold_2421_, v___x_2422_);
v___x_2424_ = lean_uint64_xor(v_fold_2421_, v___x_2423_);
v___x_2425_ = lean_uint64_to_usize(v___x_2424_);
v___x_2426_ = lean_usize_of_nat(v___x_2416_);
v___x_2427_ = ((size_t)1ULL);
v___x_2428_ = lean_usize_sub(v___x_2426_, v___x_2427_);
v___x_2429_ = lean_usize_land(v___x_2425_, v___x_2428_);
v___x_2430_ = lean_array_uget_borrowed(v_buckets_2415_, v___x_2429_);
v___x_2431_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_2414_, v___x_2430_);
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_m_2434_);
return v_res_2436_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1));
v___x_2440_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0));
v___x_2441_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2440_, v___x_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(lean_object* v_declName_2444_, uint8_t v_isMeta_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v_env_2457_; lean_object* v___y_2459_; lean_object* v___x_2472_; 
v___x_2453_ = lean_st_ref_get(v___y_2451_);
v_env_2457_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_env_2457_);
lean_dec(v___x_2453_);
v___x_2472_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2457_, v_declName_2444_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_dec_ref(v_env_2457_);
lean_dec(v_declName_2444_);
goto v___jp_2454_;
}
else
{
lean_object* v_val_2473_; lean_object* v___x_2474_; lean_object* v_modules_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_val_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_val_2473_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = l_Lean_Environment_header(v_env_2457_);
v_modules_2475_ = lean_ctor_get(v___x_2474_, 3);
lean_inc_ref(v_modules_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_array_get_size(v_modules_2475_);
v___x_2477_ = lean_nat_dec_lt(v_val_2473_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_dec_ref(v_modules_2475_);
lean_dec(v_val_2473_);
lean_dec_ref(v_env_2457_);
lean_dec(v_declName_2444_);
goto v___jp_2454_;
}
else
{
lean_object* v___x_2478_; lean_object* v_env_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___y_2483_; 
v___x_2478_ = lean_st_ref_get(v___y_2451_);
v_env_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc_ref(v_env_2479_);
lean_dec(v___x_2478_);
v___x_2480_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2);
v___x_2481_ = lean_array_fget(v_modules_2475_, v_val_2473_);
lean_dec(v_val_2473_);
lean_dec_ref(v_modules_2475_);
if (v_isMeta_2445_ == 0)
{
lean_dec_ref(v_env_2479_);
v___y_2483_ = v_isMeta_2445_;
goto v___jp_2482_;
}
else
{
uint8_t v___x_2494_; 
lean_inc(v_declName_2444_);
v___x_2494_ = l_Lean_isMarkedMeta(v_env_2479_, v_declName_2444_);
if (v___x_2494_ == 0)
{
v___y_2483_ = v_isMeta_2445_;
goto v___jp_2482_;
}
else
{
uint8_t v___x_2495_; 
v___x_2495_ = 0;
v___y_2483_ = v___x_2495_;
goto v___jp_2482_;
}
}
v___jp_2482_:
{
lean_object* v_toImport_2484_; lean_object* v_module_2485_; lean_object* v___x_2486_; 
v_toImport_2484_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_toImport_2484_);
lean_dec(v___x_2481_);
v_module_2485_ = lean_ctor_get(v_toImport_2484_, 0);
lean_inc(v_module_2485_);
lean_dec_ref(v_toImport_2484_);
lean_inc(v_declName_2444_);
v___x_2486_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_2485_, v___y_2483_, v_declName_2444_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec_ref(v___x_2486_);
v___x_2487_ = l_Lean_indirectModUseExt;
v___x_2488_ = lean_box(1);
v___x_2489_ = lean_box(0);
lean_inc_ref(v_env_2457_);
v___x_2490_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2480_, v___x_2487_, v_env_2457_, v___x_2488_, v___x_2489_);
v___x_2491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_2490_, v_declName_2444_);
lean_dec(v___x_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3));
v___y_2459_ = v___x_2492_;
goto v___jp_2458_;
}
else
{
lean_object* v_val_2493_; 
v_val_2493_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_val_2493_);
lean_dec_ref(v___x_2491_);
v___y_2459_ = v_val_2493_;
goto v___jp_2458_;
}
}
else
{
lean_dec_ref(v_env_2457_);
lean_dec(v_declName_2444_);
return v___x_2486_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
v___jp_2458_:
{
lean_object* v___x_2460_; size_t v_sz_2461_; size_t v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = lean_box(0);
v_sz_2461_ = lean_array_size(v___y_2459_);
v___x_2462_ = ((size_t)0ULL);
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_2457_, v_declName_2444_, v___y_2459_, v_sz_2461_, v___x_2462_, v___x_2460_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v_env_2457_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2463_, 0);
lean_dec(v_unused_2471_);
v___x_2465_ = v___x_2463_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v___x_2463_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2460_);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2460_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(lean_object* v_declName_2496_, lean_object* v_isMeta_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v_isMeta_boxed_2505_; lean_object* v_res_2506_; 
v_isMeta_boxed_2505_ = lean_unbox(v_isMeta_2497_);
v_res_2506_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_2496_, v_isMeta_boxed_2505_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(lean_object* v_as_x27_2507_, lean_object* v_b_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
if (lean_obj_tag(v_as_x27_2507_) == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_b_2508_);
return v___x_2516_;
}
else
{
lean_object* v_head_2517_; lean_object* v_tail_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; 
v_head_2517_ = lean_ctor_get(v_as_x27_2507_, 0);
v_tail_2518_ = lean_ctor_get(v_as_x27_2507_, 1);
v___x_2519_ = 1;
lean_inc(v_head_2517_);
v___x_2520_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_2517_, v___x_2519_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; 
lean_dec_ref(v___x_2520_);
v___x_2521_ = lean_box(0);
v_as_x27_2507_ = v_tail_2518_;
v_b_2508_ = v___x_2521_;
goto _start;
}
else
{
return v___x_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2523_, lean_object* v_b_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_2523_, v_b_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v_as_x27_2523_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(lean_object* v_currNamespace_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_currNamespace_2533_);
lean_ctor_set(v___x_2536_, 1, v___y_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_currNamespace_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(lean_object* v_x_2541_, lean_object* v___y_2542_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
v_a_2543_ = lean_ctor_get(v_x_2541_, 0);
lean_inc(v_a_2543_);
v___x_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_a_2543_);
lean_ctor_set(v___x_2544_, 1, v___y_2542_);
return v___x_2544_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_ctor_get(v_x_2541_, 0);
lean_inc(v_a_2545_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2545_);
lean_ctor_set(v___x_2546_, 1, v___y_2542_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(lean_object* v_x_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2547_, v___y_2548_);
lean_dec_ref(v_x_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(lean_object* v_env_2550_, lean_object* v_stx_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2550_, v_stx_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
if (lean_obj_tag(v_a_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
v_a_2556_ = lean_ctor_get(v___x_2554_, 1);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2554_, 0);
lean_dec(v_unused_2565_);
v___x_2558_ = v___x_2554_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2554_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_a_2556_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_val_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2594_; 
v_val_2566_ = lean_ctor_get(v_a_2555_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2568_ = v_a_2555_;
v_isShared_2569_ = v_isSharedCheck_2594_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_val_2566_);
lean_dec(v_a_2555_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2594_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_snd_2570_; 
v_snd_2570_ = lean_ctor_get(v_val_2566_, 1);
lean_inc(v_snd_2570_);
lean_dec(v_val_2566_);
if (lean_obj_tag(v_snd_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2580_; 
lean_del_object(v___x_2568_);
v_a_2571_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_a_2571_);
lean_dec_ref(v___x_2554_);
v_a_2572_ = lean_ctor_get(v_snd_2570_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_snd_2570_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2574_ = v_snd_2570_;
v_isShared_2575_ = v_isSharedCheck_2580_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v_snd_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2580_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2577_, v_a_2571_);
lean_dec_ref(v___x_2577_);
return v___x_2578_;
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2593_; 
v_a_2581_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2554_);
v_a_2582_ = lean_ctor_get(v_snd_2570_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_snd_2570_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2584_ = v_snd_2570_;
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v_snd_2570_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v_a_2582_);
v___x_2587_ = v___x_2568_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_2589_, v_a_2581_);
lean_dec_ref(v___x_2589_);
return v___x_2590_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v_a_2595_ = lean_ctor_get(v___x_2554_, 0);
v_a_2596_ = lean_ctor_get(v___x_2554_, 1);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2554_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_inc(v_a_2595_);
lean_dec(v___x_2554_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2595_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(lean_object* v_env_2604_, lean_object* v_stx_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_2604_, v_stx_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2608_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = l_Lean_maxRecDepthErrorMessage;
v___x_2615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
v___x_2617_ = l_Lean_MessageData_ofFormat(v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
v___x_2619_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2));
v___x_2620_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(lean_object* v_ref_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_ref_2621_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(lean_object* v_x_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v_env_2639_; lean_object* v_options_2640_; lean_object* v_currRecDepth_2641_; lean_object* v_maxRecDepth_2642_; lean_object* v_ref_2643_; lean_object* v_currNamespace_2644_; lean_object* v_openDecls_2645_; lean_object* v_quotContext_2646_; lean_object* v_currMacroScope_2647_; lean_object* v___x_2648_; lean_object* v_nextMacroScope_2649_; lean_object* v___f_2650_; lean_object* v___f_2651_; lean_object* v___f_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v_methods_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2638_ = lean_st_ref_get(v___y_2636_);
v_env_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref_n(v_env_2639_, 4);
lean_dec(v___x_2638_);
v_options_2640_ = lean_ctor_get(v___y_2635_, 2);
v_currRecDepth_2641_ = lean_ctor_get(v___y_2635_, 3);
v_maxRecDepth_2642_ = lean_ctor_get(v___y_2635_, 4);
v_ref_2643_ = lean_ctor_get(v___y_2635_, 5);
v_currNamespace_2644_ = lean_ctor_get(v___y_2635_, 6);
v_openDecls_2645_ = lean_ctor_get(v___y_2635_, 7);
v_quotContext_2646_ = lean_ctor_get(v___y_2635_, 10);
v_currMacroScope_2647_ = lean_ctor_get(v___y_2635_, 11);
v___x_2648_ = lean_st_ref_get(v___y_2636_);
v_nextMacroScope_2649_ = lean_ctor_get(v___x_2648_, 1);
lean_inc(v_nextMacroScope_2649_);
lean_dec(v___x_2648_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2650_, 0, v_env_2639_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2651_, 0, v_env_2639_);
lean_inc_n(v_openDecls_2645_, 2);
lean_inc_n(v_currNamespace_2644_, 3);
v___f_2652_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2652_, 0, v_env_2639_);
lean_closure_set(v___f_2652_, 1, v_currNamespace_2644_);
lean_closure_set(v___f_2652_, 2, v_openDecls_2645_);
v___f_2653_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2653_, 0, v_currNamespace_2644_);
lean_inc_ref(v_options_2640_);
v___f_2654_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2654_, 0, v_env_2639_);
lean_closure_set(v___f_2654_, 1, v_options_2640_);
lean_closure_set(v___f_2654_, 2, v_currNamespace_2644_);
lean_closure_set(v___f_2654_, 3, v_openDecls_2645_);
v_methods_2655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2655_, 0, v___f_2650_);
lean_ctor_set(v_methods_2655_, 1, v___f_2653_);
lean_ctor_set(v_methods_2655_, 2, v___f_2651_);
lean_ctor_set(v_methods_2655_, 3, v___f_2652_);
lean_ctor_set(v_methods_2655_, 4, v___f_2654_);
lean_inc(v_ref_2643_);
lean_inc(v_maxRecDepth_2642_);
lean_inc(v_currRecDepth_2641_);
lean_inc(v_currMacroScope_2647_);
lean_inc(v_quotContext_2646_);
v___x_2656_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2656_, 0, v_methods_2655_);
lean_ctor_set(v___x_2656_, 1, v_quotContext_2646_);
lean_ctor_set(v___x_2656_, 2, v_currMacroScope_2647_);
lean_ctor_set(v___x_2656_, 3, v_currRecDepth_2641_);
lean_ctor_set(v___x_2656_, 4, v_maxRecDepth_2642_);
lean_ctor_set(v___x_2656_, 5, v_ref_2643_);
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2658_, 0, v_nextMacroScope_2649_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
lean_ctor_set(v___x_2658_, 2, v___x_2657_);
v___x_2659_ = lean_apply_2(v_x_2630_, v___x_2656_, v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v_macroScope_2662_; lean_object* v_traceMsgs_2663_; lean_object* v_expandedMacroDecls_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_a_2660_);
v_a_2661_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2659_);
v_macroScope_2662_ = lean_ctor_get(v_a_2660_, 0);
lean_inc(v_macroScope_2662_);
v_traceMsgs_2663_ = lean_ctor_get(v_a_2660_, 1);
lean_inc(v_traceMsgs_2663_);
v_expandedMacroDecls_2664_ = lean_ctor_get(v_a_2660_, 2);
lean_inc(v_expandedMacroDecls_2664_);
lean_dec(v_a_2660_);
v___x_2665_ = lean_box(0);
v___x_2666_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_2664_, v___x_2665_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v_expandedMacroDecls_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2667_; lean_object* v_env_2668_; lean_object* v_ngen_2669_; lean_object* v_auxDeclNGen_2670_; lean_object* v_traceState_2671_; lean_object* v_cache_2672_; lean_object* v_messages_2673_; lean_object* v_infoState_2674_; lean_object* v_snapshotTasks_2675_; lean_object* v_newDecls_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v___x_2666_);
v___x_2667_ = lean_st_ref_take(v___y_2636_);
v_env_2668_ = lean_ctor_get(v___x_2667_, 0);
v_ngen_2669_ = lean_ctor_get(v___x_2667_, 2);
v_auxDeclNGen_2670_ = lean_ctor_get(v___x_2667_, 3);
v_traceState_2671_ = lean_ctor_get(v___x_2667_, 4);
v_cache_2672_ = lean_ctor_get(v___x_2667_, 5);
v_messages_2673_ = lean_ctor_get(v___x_2667_, 6);
v_infoState_2674_ = lean_ctor_get(v___x_2667_, 7);
v_snapshotTasks_2675_ = lean_ctor_get(v___x_2667_, 8);
v_newDecls_2676_ = lean_ctor_get(v___x_2667_, 9);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2667_, 1);
lean_dec(v_unused_2703_);
v___x_2678_ = v___x_2667_;
v_isShared_2679_ = v_isSharedCheck_2702_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_newDecls_2676_);
lean_inc(v_snapshotTasks_2675_);
lean_inc(v_infoState_2674_);
lean_inc(v_messages_2673_);
lean_inc(v_cache_2672_);
lean_inc(v_traceState_2671_);
lean_inc(v_auxDeclNGen_2670_);
lean_inc(v_ngen_2669_);
lean_inc(v_env_2668_);
lean_dec(v___x_2667_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2702_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v_macroScope_2662_);
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_env_2668_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_macroScope_2662_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_ngen_2669_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_auxDeclNGen_2670_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_traceState_2671_);
lean_ctor_set(v_reuseFailAlloc_2701_, 5, v_cache_2672_);
lean_ctor_set(v_reuseFailAlloc_2701_, 6, v_messages_2673_);
lean_ctor_set(v_reuseFailAlloc_2701_, 7, v_infoState_2674_);
lean_ctor_set(v_reuseFailAlloc_2701_, 8, v_snapshotTasks_2675_);
lean_ctor_set(v_reuseFailAlloc_2701_, 9, v_newDecls_2676_);
v___x_2681_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_st_ref_set(v___y_2636_, v___x_2681_);
v___x_2683_ = l_List_reverse___redArg(v_traceMsgs_2663_);
v___x_2684_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_2683_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2692_);
v___x_2686_ = v___x_2684_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v___x_2684_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v_a_2661_);
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2661_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_a_2661_);
v_a_2693_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2684_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2684_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_traceMsgs_2663_);
lean_dec(v_macroScope_2662_);
lean_dec(v_a_2661_);
v_a_2704_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2666_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2666_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2712_; 
v_a_2712_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2659_);
if (lean_obj_tag(v_a_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_a_2713_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_a_2713_);
v_a_2714_ = lean_ctor_get(v_a_2712_, 1);
lean_inc_ref(v_a_2714_);
lean_dec_ref(v_a_2712_);
v___x_2715_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0));
v___x_2716_ = lean_string_dec_eq(v_a_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2717_, 0, v_a_2714_);
v___x_2718_ = l_Lean_MessageData_ofFormat(v___x_2717_);
v___x_2719_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_2713_, v___x_2718_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v_a_2713_);
return v___x_2719_;
}
else
{
lean_object* v___x_2720_; 
lean_dec_ref(v_a_2714_);
v___x_2720_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_2713_);
return v___x_2720_;
}
}
else
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
return v___x_2721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2730_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_box(0);
v___x_2735_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75));
v___x_2736_ = l_Lean_mkConst(v___x_2735_, v___x_2734_);
return v___x_2736_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6));
v___x_2747_ = l_Lean_mkConst(v___x_2746_, v___x_2745_);
return v___x_2747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(uint8_t v___x_2750_, lean_object* v_as_2751_, size_t v_sz_2752_, size_t v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_a_2763_; uint8_t v___x_2767_; 
v___x_2767_ = lean_usize_dec_lt(v_i_2753_, v_sz_2752_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_b_2754_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v_a_2771_; uint8_t v___x_2772_; 
v___x_2769_ = ((lean_object*)(l_Lean_Widget_showWidgetSpec___closed__1));
v___x_2770_ = lean_box(0);
v_a_2771_ = lean_array_uget_borrowed(v_as_2751_, v_i_2753_);
lean_inc(v_a_2771_);
v___x_2772_ = l_Lean_Syntax_isOfKind(v_a_2771_, v___x_2769_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_dec_ref(v___x_2773_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2773_;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2774_ = lean_unsigned_to_nat(0u);
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = l_Lean_Syntax_getArg(v_a_2771_, v___x_2774_);
v___x_2777_ = ((lean_object*)(l_Lean_Widget_eraseWidgetSpec___closed__1));
lean_inc(v___x_2776_);
v___x_2778_ = l_Lean_Syntax_isOfKind(v___x_2776_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__1));
lean_inc(v___x_2776_);
v___x_2780_ = l_Lean_Syntax_isOfKind(v___x_2776_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
lean_dec(v___x_2776_);
v___x_2781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_dec_ref(v___x_2781_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2781_;
}
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_2774_);
v___x_2783_ = ((lean_object*)(l_Lean_Widget_addWidgetSpec___closed__3));
lean_inc(v___x_2782_);
v___x_2784_ = l_Lean_Syntax_isOfKind(v___x_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; 
lean_dec(v___x_2782_);
lean_dec(v___x_2776_);
v___x_2785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_dec_ref(v___x_2785_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2786_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_2775_);
lean_dec(v___x_2776_);
v___x_2787_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__3));
lean_inc(v___x_2786_);
v___x_2788_ = l_Lean_Syntax_isOfKind(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
lean_dec(v___x_2786_);
lean_dec(v___x_2782_);
v___x_2789_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref(v___x_2789_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2789_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2790_, 0, v___x_2782_);
v___x_2791_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_2790_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2791_);
v___x_2793_ = l_Lean_Widget_elabWidgetInstanceSpec(v___x_2786_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_n(v_a_2794_, 2);
lean_dec_ref(v___x_2793_);
v___x_2795_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_2794_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2795_) == 0)
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_unbox(v_a_2792_);
if (v___x_2796_ == 1)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2792_);
v_a_2797_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2795_);
v___x_2798_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_2797_, v___y_2758_, v___y_2760_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_dec_ref(v___x_2798_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2798_;
}
}
else
{
lean_object* v_a_2799_; lean_object* v_id_2800_; uint64_t v_javascriptHash_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2799_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2795_);
v_id_2800_ = lean_ctor_get(v_a_2799_, 0);
lean_inc(v_id_2800_);
v_javascriptHash_2801_ = lean_ctor_get_uint64(v_a_2799_, sizeof(void*)*2);
lean_dec(v_a_2799_);
v___x_2802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1));
v___x_2803_ = l_Lean_Name_append(v_id_2800_, v___x_2802_);
v___x_2804_ = l_Lean_Core_mkFreshUserName(v___x_2803_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2804_);
v___x_2806_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_2794_, v___y_2758_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; uint8_t v___x_2827_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref(v___x_2806_);
v___x_2808_ = lean_box(0);
v___x_2827_ = l_Lean_Expr_hasMVar(v_a_2807_);
if (v___x_2827_ == 0)
{
v___y_2810_ = v___y_2755_;
v___y_2811_ = v___y_2756_;
v___y_2812_ = v___y_2757_;
v___y_2813_ = v___y_2758_;
v___y_2814_ = v___y_2759_;
v___y_2815_ = v___y_2760_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
lean_inc(v_a_2807_);
v___x_2829_ = l_Lean_indentExpr(v_a_2807_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_2830_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref(v___x_2831_);
v___y_2810_ = v___y_2755_;
v___y_2811_ = v___y_2756_;
v___y_2812_ = v___y_2757_;
v___y_2813_ = v___y_2758_;
v___y_2814_ = v___y_2759_;
v___y_2815_ = v___y_2760_;
goto v___jp_2809_;
}
else
{
lean_dec(v_a_2807_);
lean_dec(v_a_2805_);
lean_dec(v_a_2792_);
return v___x_2831_;
}
}
v___jp_2809_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
lean_inc_n(v_a_2805_, 2);
v___x_2817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2805_);
lean_ctor_set(v___x_2817_, 1, v___x_2808_);
lean_ctor_set(v___x_2817_, 2, v___x_2816_);
v___x_2818_ = lean_box(0);
v___x_2819_ = 1;
v___x_2820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_a_2805_);
lean_ctor_set(v___x_2820_, 1, v___x_2808_);
v___x_2821_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2817_);
lean_ctor_set(v___x_2821_, 1, v_a_2807_);
lean_ctor_set(v___x_2821_, 2, v___x_2818_);
lean_ctor_set(v___x_2821_, 3, v___x_2820_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*4, v___x_2819_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
v___x_2823_ = l_Lean_addAndCompile(v___x_2822_, v___x_2750_, v___x_2778_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2823_) == 0)
{
uint8_t v___x_2824_; 
lean_dec_ref(v___x_2823_);
v___x_2824_ = lean_unbox(v_a_2792_);
lean_dec(v_a_2792_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_2801_, v_a_2805_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref(v___x_2825_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2825_;
}
}
else
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_2801_, v_a_2805_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_dec_ref(v___x_2826_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2826_;
}
}
}
else
{
lean_dec(v_a_2805_);
lean_dec(v_a_2792_);
return v___x_2823_;
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2805_);
lean_dec(v_a_2792_);
v_a_2832_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2806_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2806_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2792_);
v_a_2840_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2804_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2804_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2792_);
v_a_2848_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2795_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2795_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2792_);
v_a_2856_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2793_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2793_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v___x_2786_);
v_a_2864_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2791_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2791_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2872_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_2775_);
lean_dec(v___x_2776_);
v___x_2873_ = ((lean_object*)(l_Lean_Widget_widgetInstanceSpec___closed__7));
lean_inc(v___x_2872_);
v___x_2874_ = l_Lean_Syntax_isOfKind(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_dec(v___x_2872_);
v___x_2875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref(v___x_2875_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2875_;
}
}
else
{
lean_object* v_ref_2876_; lean_object* v_quotContext_2877_; lean_object* v_currMacroScope_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_ref_2876_ = lean_ctor_get(v___y_2759_, 5);
v_quotContext_2877_ = lean_ctor_get(v___y_2759_, 10);
v_currMacroScope_2878_ = lean_ctor_get(v___y_2759_, 11);
v___x_2879_ = 0;
v___x_2880_ = l_Lean_SourceInfo_fromRef(v_ref_2876_, v___x_2879_);
v___x_2881_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48));
v___x_2882_ = lean_obj_once(&l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50, &l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once, _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
v___x_2883_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53));
lean_inc(v_currMacroScope_2878_);
lean_inc(v_quotContext_2877_);
v___x_2884_ = l_Lean_addMacroScope(v_quotContext_2877_, v___x_2883_, v_currMacroScope_2878_);
v___x_2885_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56));
lean_inc_n(v___x_2880_, 2);
v___x_2886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2880_);
lean_ctor_set(v___x_2886_, 1, v___x_2882_);
lean_ctor_set(v___x_2886_, 2, v___x_2884_);
lean_ctor_set(v___x_2886_, 3, v___x_2885_);
v___x_2887_ = ((lean_object*)(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6));
v___x_2888_ = l_Lean_Syntax_node1(v___x_2880_, v___x_2887_, v___x_2872_);
v___x_2889_ = l_Lean_Syntax_node2(v___x_2880_, v___x_2881_, v___x_2886_, v___x_2888_);
v___x_2890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
v___x_2891_ = l_Lean_Elab_Term_elabTerm(v___x_2889_, v___x_2890_, v___x_2750_, v___x_2750_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_2892_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; uint64_t v_javascriptHash_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
v_javascriptHash_2895_ = lean_ctor_get_uint64(v_a_2894_, sizeof(void*)*1);
lean_dec(v_a_2894_);
v___x_2896_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_2895_, v___y_2758_, v___y_2760_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_dec_ref(v___x_2896_);
v_a_2763_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
return v___x_2896_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2893_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2893_);
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
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
v_a_2905_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2891_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2891_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
}
v___jp_2762_:
{
size_t v___x_2764_; size_t v___x_2765_; 
v___x_2764_ = ((size_t)1ULL);
v___x_2765_ = lean_usize_add(v_i_2753_, v___x_2764_);
v_i_2753_ = v___x_2765_;
v_b_2754_ = v_a_2763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(lean_object* v___x_2913_, lean_object* v_as_2914_, lean_object* v_sz_2915_, lean_object* v_i_2916_, lean_object* v_b_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
uint8_t v___x_34631__boxed_2925_; size_t v_sz_boxed_2926_; size_t v_i_boxed_2927_; lean_object* v_res_2928_; 
v___x_34631__boxed_2925_ = lean_unbox(v___x_2913_);
v_sz_boxed_2926_ = lean_unbox_usize(v_sz_2915_);
lean_dec(v_sz_2915_);
v_i_boxed_2927_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_34631__boxed_2925_, v_as_2914_, v_sz_boxed_2926_, v_i_boxed_2927_, v_b_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v_as_2914_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(uint8_t v___x_2929_, lean_object* v___x_2930_, size_t v_sz_2931_, size_t v___x_2932_, lean_object* v___x_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_2929_, v___x_2930_, v_sz_2931_, v___x_2932_, v___x_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; 
v_unused_2949_ = lean_ctor_get(v___x_2941_, 0);
lean_dec(v_unused_2949_);
v___x_2943_ = v___x_2941_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_dec(v___x_2941_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2933_);
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2933_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(lean_object* v___x_2950_, lean_object* v___x_2951_, lean_object* v_sz_2952_, lean_object* v___x_2953_, lean_object* v___x_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v___x_34983__boxed_2962_; size_t v_sz_boxed_2963_; size_t v___x_34985__boxed_2964_; lean_object* v_res_2965_; 
v___x_34983__boxed_2962_ = lean_unbox(v___x_2950_);
v_sz_boxed_2963_ = lean_unbox_usize(v_sz_2952_);
lean_dec(v_sz_2952_);
v___x_34985__boxed_2964_ = lean_unbox_usize(v___x_2953_);
lean_dec(v___x_2953_);
v_res_2965_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(v___x_34983__boxed_2962_, v___x_2951_, v_sz_boxed_2963_, v___x_34985__boxed_2964_, v___x_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v___x_2951_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd(lean_object* v_x_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_Lean_Widget_showPanelWidgetsCmd___closed__1));
lean_inc(v_x_2968_);
v___x_2973_ = l_Lean_Syntax_isOfKind(v_x_2968_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec(v_x_2968_);
v___x_2974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_ws_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; size_t v_sz_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; 
v___x_2975_ = lean_unsigned_to_nat(2u);
v___x_2976_ = l_Lean_Syntax_getArg(v_x_2968_, v___x_2975_);
lean_dec(v_x_2968_);
v_ws_2977_ = l_Lean_Syntax_getArgs(v___x_2976_);
lean_dec(v___x_2976_);
v___x_2978_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_2977_);
lean_dec_ref(v_ws_2977_);
v___x_2979_ = lean_box(0);
v_sz_2980_ = lean_array_size(v___x_2978_);
v___x_2981_ = lean_box(v___x_2973_);
v___x_2982_ = lean_box_usize(v_sz_2980_);
v___x_2983_ = ((lean_object*)(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1));
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2984_, 0, v___x_2981_);
lean_closure_set(v___f_2984_, 1, v___x_2978_);
lean_closure_set(v___f_2984_, 2, v___x_2982_);
lean_closure_set(v___f_2984_, 3, v___x_2983_);
lean_closure_set(v___f_2984_, 4, v___x_2979_);
v___x_2985_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2984_, v_a_2969_, v_a_2970_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(lean_object* v_x_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(lean_object* v_00_u03b1_2991_, lean_object* v_x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_2992_, v___y_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2996_, lean_object* v_x_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_2996_, v_x_2997_, v___y_2998_, v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_x_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(lean_object* v_00_u03b1_3001_, lean_object* v_ref_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_3002_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_ref_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_3011_, v_ref_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(lean_object* v_00_u03b1_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v_x_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(lean_object* v_00_u03b1_3031_, lean_object* v_x_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(v_00_u03b1_3031_, v_x_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(lean_object* v_wi_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_3041_, v___y_3045_, v___y_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(lean_object* v_wi_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(v_wi_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(lean_object* v_00_u03b1_3059_, lean_object* v_00_u03b2_3060_, lean_object* v_00_u03c3_3061_, lean_object* v_ext_3062_, lean_object* v_b_3063_, uint8_t v_kind_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_3062_, v_b_3063_, v_kind_3064_, v___y_3068_, v___y_3069_, v___y_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(lean_object* v_00_u03b1_3073_, lean_object* v_00_u03b2_3074_, lean_object* v_00_u03c3_3075_, lean_object* v_ext_3076_, lean_object* v_b_3077_, lean_object* v_kind_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v_kind_boxed_3086_; lean_object* v_res_3087_; 
v_kind_boxed_3086_ = lean_unbox(v_kind_3078_);
v_res_3087_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_3073_, v_00_u03b2_3074_, v_00_u03c3_3075_, v_ext_3076_, v_b_3077_, v_kind_boxed_3086_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(lean_object* v_00_u03b1_3088_, lean_object* v_msg_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v_msg_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(lean_object* v_00_u03b1_3098_, lean_object* v_msg_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(v_00_u03b1_3098_, v_msg_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(uint64_t v_h_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_3108_, v___y_3112_, v___y_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(lean_object* v_h_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint64_t v_h_boxed_3125_; lean_object* v_res_3126_; 
v_h_boxed_3125_ = lean_unbox_uint64(v_h_3117_);
lean_dec_ref(v_h_3117_);
v_res_3126_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(v_h_boxed_3125_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(lean_object* v_cls_3127_, lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_3127_, v_msg_3128_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(lean_object* v_cls_3137_, lean_object* v_msg_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_3137_, v_msg_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(lean_object* v_as_3147_, lean_object* v_as_x27_3148_, lean_object* v_b_3149_, lean_object* v_a_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_3148_, v_b_3149_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(lean_object* v_as_3159_, lean_object* v_as_x27_3160_, lean_object* v_b_3161_, lean_object* v_a_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_3159_, v_as_x27_3160_, v_b_3161_, v_a_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v_as_x27_3160_);
lean_dec(v_as_3159_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(lean_object* v_00_u03b1_3171_, lean_object* v_ref_3172_, lean_object* v_msg_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_3172_, v_msg_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3182_, lean_object* v_ref_3183_, lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_3182_, v_ref_3183_, v_msg_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v_ref_3183_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(lean_object* v_00_u03b4_3193_, lean_object* v_t_3194_, uint64_t v_k_3195_, lean_object* v_fallback_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_3194_, v_k_3195_, v_fallback_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(lean_object* v_00_u03b4_3198_, lean_object* v_t_3199_, lean_object* v_k_3200_, lean_object* v_fallback_3201_){
_start:
{
uint64_t v_k_boxed_3202_; lean_object* v_res_3203_; 
v_k_boxed_3202_ = lean_unbox_uint64(v_k_3200_);
lean_dec_ref(v_k_3200_);
v_res_3203_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_3198_, v_t_3199_, v_k_boxed_3202_, v_fallback_3201_);
lean_dec(v_fallback_3201_);
lean_dec(v_t_3199_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(lean_object* v_00_u03b2_3204_, uint64_t v_k_3205_, lean_object* v_v_3206_, lean_object* v_t_3207_, lean_object* v_hl_3208_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_3205_, v_v_3206_, v_t_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(lean_object* v_00_u03b2_3210_, lean_object* v_k_3211_, lean_object* v_v_3212_, lean_object* v_t_3213_, lean_object* v_hl_3214_){
_start:
{
uint64_t v_k_boxed_3215_; lean_object* v_res_3216_; 
v_k_boxed_3215_ = lean_unbox_uint64(v_k_3211_);
lean_dec_ref(v_k_3211_);
v_res_3216_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_3210_, v_k_boxed_3215_, v_v_3212_, v_t_3213_, v_hl_3214_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(lean_object* v_msgData_3217_, lean_object* v_macroStack_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_3217_, v_macroStack_3218_, v___y_3223_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(lean_object* v_msgData_3227_, lean_object* v_macroStack_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_3227_, v_macroStack_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(lean_object* v_00_u03b2_3237_, uint64_t v_k_3238_, lean_object* v_t_3239_, lean_object* v_h_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3238_, v_t_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(lean_object* v_00_u03b2_3242_, lean_object* v_k_3243_, lean_object* v_t_3244_, lean_object* v_h_3245_){
_start:
{
uint64_t v_k_boxed_3246_; lean_object* v_res_3247_; 
v_k_boxed_3246_ = lean_unbox_uint64(v_k_3243_);
lean_dec_ref(v_k_3243_);
v_res_3247_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_3242_, v_k_boxed_3246_, v_t_3244_, v_h_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3248_, lean_object* v_m_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_3249_, v_a_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3252_, lean_object* v_m_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_3252_, v_m_3253_, v_a_3254_);
lean_dec(v_a_3254_);
lean_dec_ref(v_m_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(lean_object* v_00_u03b2_3256_, lean_object* v_x_3257_, lean_object* v_x_3258_){
_start:
{
uint8_t v___x_3259_; 
v___x_3259_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_3257_, v_x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_){
_start:
{
uint8_t v_res_3263_; lean_object* v_r_3264_; 
v_res_3263_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_3260_, v_x_3261_, v_x_3262_);
lean_dec_ref(v_x_3262_);
lean_dec_ref(v_x_3261_);
v_r_3264_ = lean_box(v_res_3263_);
return v_r_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(lean_object* v_00_u03b2_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_3266_, v_x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_a_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_3269_, v_a_3270_, v_x_3271_);
lean_dec(v_x_3271_);
lean_dec(v_a_3270_);
return v_res_3272_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, size_t v_x_3275_, lean_object* v_x_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_3274_, v_x_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
size_t v_x_35347__boxed_3282_; uint8_t v_res_3283_; lean_object* v_r_3284_; 
v_x_35347__boxed_3282_ = lean_unbox_usize(v_x_3280_);
lean_dec(v_x_3280_);
v_res_3283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_3278_, v_x_3279_, v_x_35347__boxed_3282_, v_x_3281_);
lean_dec_ref(v_x_3281_);
lean_dec_ref(v_x_3279_);
v_r_3284_ = lean_box(v_res_3283_);
return v_r_3284_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(lean_object* v_00_u03b2_3285_, lean_object* v_keys_3286_, lean_object* v_vals_3287_, lean_object* v_heq_3288_, lean_object* v_i_3289_, lean_object* v_k_3290_){
_start:
{
uint8_t v___x_3291_; 
v___x_3291_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_3286_, v_i_3289_, v_k_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(lean_object* v_00_u03b2_3292_, lean_object* v_keys_3293_, lean_object* v_vals_3294_, lean_object* v_heq_3295_, lean_object* v_i_3296_, lean_object* v_k_3297_){
_start:
{
uint8_t v_res_3298_; lean_object* v_r_3299_; 
v_res_3298_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_3292_, v_keys_3293_, v_vals_3294_, v_heq_3295_, v_i_3296_, v_k_3297_);
lean_dec_ref(v_k_3297_);
lean_dec_ref(v_vals_3294_);
lean_dec_ref(v_keys_3293_);
v_r_3299_ = lean_box(v_res_3298_);
return v_r_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0(lean_object* v_s_3317_, lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Widget_elabWidgetInstanceSpec(v_s_3317_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_3327_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; uint64_t v_javascriptHash_3330_; lean_object* v_props_3331_; lean_object* v___x_3332_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v_javascriptHash_3330_ = lean_ctor_get_uint64(v_a_3329_, sizeof(void*)*2);
v_props_3331_ = lean_ctor_get(v_a_3329_, 1);
lean_inc_ref(v_props_3331_);
lean_dec(v_a_3329_);
v___x_3332_ = l_Lean_Widget_savePanelWidgetInfo(v_javascriptHash_3330_, v_props_3331_, v_x_3318_, v___y_3323_, v___y_3324_);
return v___x_3332_;
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v_x_3318_);
v_a_3333_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3328_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3328_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v_x_3318_);
v_a_3341_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3326_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3326_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___lam__0___boxed(lean_object* v_s_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Widget_elabWidgetCmd___lam__0(v_s_3349_, v_x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd(lean_object* v_x_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_Lean_Widget_widgetCmd___closed__1));
lean_inc(v_x_3359_);
v___x_3364_ = l_Lean_Syntax_isOfKind(v_x_3359_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec(v_x_3359_);
v___x_3365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; lean_object* v_s_3367_; lean_object* v___f_3368_; lean_object* v___x_3369_; 
v___x_3366_ = lean_unsigned_to_nat(1u);
v_s_3367_ = l_Lean_Syntax_getArg(v_x_3359_, v___x_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_Widget_elabWidgetCmd___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3368_, 0, v_s_3367_);
lean_closure_set(v___f_3368_, 1, v_x_3359_);
v___x_3369_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3368_, v_a_3360_, v_a_3361_);
return v___x_3369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_elabWidgetCmd___boxed(lean_object* v_x_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_Widget_elabWidgetCmd(v_x_3370_, v_a_3371_, v_a_3372_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
return v_res_3374_;
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
