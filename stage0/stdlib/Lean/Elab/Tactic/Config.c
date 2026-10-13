// Lean compiler output
// Module: Lean.Elab.Tactic.Config
// Imports: public import Lean.Elab.ConfigEval import Lean.Linter.MissingDocs
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedStructureFieldInfo_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(230, 254, 59, 95, 54, 234, 162, 220)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(207, 146, 87, 28, 198, 178, 209, 199)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "valConfigItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(135, 67, 19, 169, 17, 95, 109, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "negConfigItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(196, 29, 29, 161, 247, 206, 181, 221)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__20_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Internal error: Failed to access field `"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` in parent structure"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Structure `"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` does not have a field named `"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is not a structure"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Field `"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` of structure `"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Invalid configuration field"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__9_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(247, 100, 102, 194, 167, 62, 107, 182)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__13_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__15_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__17_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__19_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__18_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__21_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__22_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__14_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__23_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__10_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__24_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Unhygienic.run"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Unhygienic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(197, 173, 144, 140, 214, 209, 181, 177)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(147, 53, 81, 9, 23, 50, 162, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 253, 188, 127, 247, 56, 12, 45)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(22, 170, 5, 122, 36, 116, 111, 9)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(116, 123, 139, 164, 173, 191, 116, 242)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__26_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__28_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___boxed(lean_object**);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Option is not boolean-valued, so `("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " := ...)` syntax must be used"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_elabConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_elabConfig___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabConfig___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabConfig___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_elabConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabConfig___closed__2;
static const lean_ctor_object l_Lean_Elab_Tactic_elabConfig___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_elabConfig___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_elabConfig___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(79, 160, 60, 55, 136, 115, 80, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__9_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalUnsafe"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11_value),LEAN_SCALAR_PTR_LITERAL(58, 22, 240, 194, 84, 11, 157, 28)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__14_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__16_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__24_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__25_value),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__27_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__29_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "TermElabM"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31_value),LEAN_SCALAR_PTR_LITERAL(254, 202, 244, 160, 13, 113, 42, 61)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31_value),LEAN_SCALAR_PTR_LITERAL(85, 85, 78, 208, 80, 136, 131, 165)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__35_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__37 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__37_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__37_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Meta.evalExpr'"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalExpr'"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__41 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__41_value),LEAN_SCALAR_PTR_LITERAL(72, 197, 199, 196, 61, 231, 242, 161)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__41_value),LEAN_SCALAR_PTR_LITERAL(45, 28, 27, 131, 3, 60, 106, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__44 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__46 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__46_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__46_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "safety"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48_value),LEAN_SCALAR_PTR_LITERAL(214, 232, 200, 99, 138, 69, 150, 214)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__51 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__51_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__51_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 119, 170, 15, 163, 222, 21)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__56 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__56_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__56_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__58 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__58_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__59 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__59_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__58_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__59_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__61 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__61_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__61_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__64 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__64_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__64_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__66 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__66_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__66_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__68 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__68_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__69 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__69_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__68_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__69_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75_value),LEAN_SCALAR_PTR_LITERAL(111, 217, 152, 21, 13, 97, 204, 102)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77_value),LEAN_SCALAR_PTR_LITERAL(12, 151, 53, 232, 164, 85, 213, 132)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__80 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__80_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__80_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83_value),LEAN_SCALAR_PTR_LITERAL(152, 202, 61, 94, 207, 219, 212, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__86_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__87 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__87_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__87_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89_value),LEAN_SCALAR_PTR_LITERAL(20, 187, 205, 103, 159, 89, 197, 217)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__93 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__93_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__92_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__94 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__94_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__94_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__95 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__95_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__93_value),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__95_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__99 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__99_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__99_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__101 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__101_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__101_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__103 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__103_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__103_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__106 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__106_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__106_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__108 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__108_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__108_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__110 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__110_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__110_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__112 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__112_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__112_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114_value),LEAN_SCALAR_PTR_LITERAL(207, 177, 38, 2, 101, 67, 237, 158)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "go"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117_value),LEAN_SCALAR_PTR_LITERAL(205, 171, 144, 64, 100, 57, 169, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__120 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__120_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__120_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "withRef"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122_value),LEAN_SCALAR_PTR_LITERAL(193, 74, 233, 14, 30, 198, 157, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__125_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122_value),LEAN_SCALAR_PTR_LITERAL(128, 176, 237, 189, 54, 129, 101, 238)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__125 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__125_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__125_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__126 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__126_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__126_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "items"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128_value),LEAN_SCALAR_PTR_LITERAL(253, 151, 36, 233, 185, 66, 64, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mkConfigItemViews"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131_value),LEAN_SCALAR_PTR_LITERAL(63, 71, 46, 101, 82, 184, 97, 36)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131_value),LEAN_SCALAR_PTR_LITERAL(13, 58, 92, 35, 220, 254, 65, 28)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__134_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__135 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__135_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__135_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__137 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__137_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__137_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "getConfigItems"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139_value),LEAN_SCALAR_PTR_LITERAL(165, 227, 1, 114, 3, 24, 132, 2)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139_value),LEAN_SCALAR_PTR_LITERAL(188, 7, 61, 21, 19, 183, 210, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__142_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__143 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__143_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__143_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__145 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__145_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__145_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__148 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__148_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__148_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "items.isEmpty"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isEmpty"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__152 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__152_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128_value),LEAN_SCALAR_PTR_LITERAL(253, 151, 36, 233, 185, 66, 64, 186)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__152_value),LEAN_SCALAR_PTR_LITERAL(120, 44, 13, 235, 124, 131, 129, 28)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__155 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__155_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__155_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__158 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__158_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__158_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unless"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__161 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__161_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__161_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__163 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__163_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__163_value),LEAN_SCALAR_PTR_LITERAL(115, 27, 24, 243, 204, 49, 153, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__166 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__166_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__166_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "getEnv"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168_value),LEAN_SCALAR_PTR_LITERAL(72, 61, 95, 191, 209, 198, 184, 155)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MonadEnv"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__171 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__171_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__171_value),LEAN_SCALAR_PTR_LITERAL(39, 26, 63, 127, 255, 220, 234, 209)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168_value),LEAN_SCALAR_PTR_LITERAL(196, 158, 45, 33, 7, 23, 65, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__172_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__173 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__173_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__173_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "contains"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175_value),LEAN_SCALAR_PTR_LITERAL(18, 123, 184, 228, 187, 249, 197, 66)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "termThrowError__"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__178 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__178_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__178_value),LEAN_SCALAR_PTR_LITERAL(225, 45, 105, 121, 242, 5, 105, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "throwError"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__181 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__181_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__181_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__184 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__184_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__184_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "interpolatedStrLitKind"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__186 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__186_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__186_value),LEAN_SCALAR_PTR_LITERAL(216, 181, 130, 246, 88, 58, 26, 43)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "\"Error evaluating configuration: Environment does not yet contain type {"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "}\""};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "recordExtraModUseFromDecl"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190_value),LEAN_SCALAR_PTR_LITERAL(179, 191, 95, 105, 231, 201, 129, 17)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190_value),LEAN_SCALAR_PTR_LITERAL(226, 145, 141, 90, 46, 229, 100, 51)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__194 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__194_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__193_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__195 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__195_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__195_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__196 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__196_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__194_value),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__196_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198_value),LEAN_SCALAR_PTR_LITERAL(249, 28, 190, 209, 3, 53, 190, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__203 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__203_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__203_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__205 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__205_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__205_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__207 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__207_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__207_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212_value),LEAN_SCALAR_PTR_LITERAL(96, 29, 49, 50, 208, 186, 243, 35)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212_value),LEAN_SCALAR_PTR_LITERAL(130, 54, 132, 213, 25, 246, 70, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__216 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__216_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__215_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__217 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__217_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__217_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__218 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__218_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__216_value),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__218_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "c.hasSyntheticSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "hasSyntheticSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__222 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__222_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__222_value),LEAN_SCALAR_PTR_LITERAL(210, 106, 4, 63, 158, 26, 42, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "c.hasSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hasSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__226 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__226_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__226_value),LEAN_SCALAR_PTR_LITERAL(6, 197, 62, 134, 67, 16, 33, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\"Configuration contains `sorry`\""};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__229 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__229_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__229_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "res"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232_value),LEAN_SCALAR_PTR_LITERAL(88, 61, 90, 23, 143, 26, 140, 228)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__235 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__235_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__235_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "catch"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ex"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238_value),LEAN_SCALAR_PTR_LITERAL(184, 45, 58, 6, 126, 47, 125, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "msg"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242_value),LEAN_SCALAR_PTR_LITERAL(178, 178, 148, 59, 81, 15, 45, 82)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\"Error evaluating configuration\\n{"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indentD"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246_value),LEAN_SCALAR_PTR_LITERAL(50, 104, 185, 197, 237, 222, 231, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__249_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__249_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246_value),LEAN_SCALAR_PTR_LITERAL(99, 57, 37, 59, 181, 202, 46, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__249 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__249_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__249_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__250 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__250_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__250_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "}\\n\\nException: {"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ex.toMessageData"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toMessageData"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__255 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__255_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238_value),LEAN_SCALAR_PTR_LITERAL(184, 45, 58, 6, 126, 47, 125, 220)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__255_value),LEAN_SCALAR_PTR_LITERAL(65, 100, 242, 87, 108, 175, 178, 247)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__259 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__259_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__259_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "logError"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261_value),LEAN_SCALAR_PTR_LITERAL(214, 35, 121, 239, 202, 177, 52, 200)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__264_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__264_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261_value),LEAN_SCALAR_PTR_LITERAL(191, 29, 240, 150, 76, 145, 45, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__264 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__264_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__264_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__265 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__265_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__265_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_configElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configElab"};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 113, 199, 142, 5, 77, 11, 142)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_configElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_configElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_configElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__6_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_configElab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "declare_config_elab_legacy"};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__10_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__11_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__20_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__12_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__13_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__14_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__13_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_configElab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__15_value)}};
static const lean_object* l_Lean_Elab_Tactic_configElab___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__16_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_configElab = (const lean_object*)&l_Lean_Elab_Tactic_configElab___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "read"};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 16, 165, 175, 2, 23, 214, 231)}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadReader"};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 173, 117, 41, 17, 79, 142, 168)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 74, 177, 199, 30, 224, 37, 71)}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TacticM"};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 63, 151, 54, 27, 84, 190, 214)}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9;
static const lean_string_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "config elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_commandConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "commandConfigElab"};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 198, 218, 173, 29, 96, 128, 77)}};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_commandConfigElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "declare_command_config_elab_legacy"};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__13_value)}};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_configElab___closed__13_value)}};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_commandConfigElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_commandConfigElab___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_commandConfigElab = (const lean_object*)&l_Lean_Elab_Tactic_commandConfigElab___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommandElabM"};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 183, 159, 6, 104, 246, 8, 218)}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2;
static const lean_string_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "liftTermElabM"};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 112, 220, 86, 129, 53, 91, 11)}};
static const lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0(size_t v_sz_48_, size_t v_i_49_, lean_object* v_bs_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = lean_usize_dec_lt(v_i_49_, v_sz_48_);
if (v___x_51_ == 0)
{
return v_bs_50_;
}
else
{
lean_object* v_v_52_; lean_object* v___x_53_; lean_object* v_bs_x27_54_; lean_object* v___y_56_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_v_52_ = lean_array_uget(v_bs_50_, v_i_49_);
v___x_53_ = lean_unsigned_to_nat(0u);
v_bs_x27_54_ = lean_array_uset(v_bs_50_, v_i_49_, v___x_53_);
v___x_61_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__4));
lean_inc(v_v_52_);
v___x_62_ = l_Lean_Syntax_isOfKind(v_v_52_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__6));
lean_inc(v_v_52_);
v___x_64_ = l_Lean_Syntax_isOfKind(v_v_52_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_66_, 0, v_v_52_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
lean_ctor_set(v___x_66_, 2, v___x_65_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*3, v___x_64_);
v___y_56_ = v___x_66_;
goto v___jp_55_;
}
else
{
lean_object* v___x_67_; lean_object* v_tk_68_; lean_object* v___x_69_; lean_object* v_value_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v_tk_68_ = l_Lean_Syntax_getArg(v_v_52_, v___x_67_);
v___x_69_ = lean_unsigned_to_nat(3u);
v_value_70_ = l_Lean_Syntax_getArg(v_v_52_, v___x_69_);
v___x_71_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7));
v___x_72_ = l_Lean_mkCIdentFrom(v_tk_68_, v___x_71_, v___x_62_);
lean_dec(v_tk_68_);
v___x_73_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_73_, 0, v_v_52_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_ctor_set(v___x_73_, 2, v_value_70_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*3, v___x_62_);
v___y_56_ = v___x_73_;
goto v___jp_55_;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = l_Lean_Syntax_getArg(v_v_52_, v___x_53_);
v___x_75_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__9));
lean_inc(v___x_74_);
v___x_76_ = l_Lean_Syntax_isOfKind(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__11));
lean_inc(v___x_74_);
v___x_78_ = l_Lean_Syntax_isOfKind(v___x_74_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__13));
lean_inc(v___x_74_);
v___x_80_ = l_Lean_Syntax_isOfKind(v___x_74_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v___x_74_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_82_, 0, v_v_52_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*3, v___x_80_);
v___y_56_ = v___x_82_;
goto v___jp_55_;
}
else
{
lean_object* v___x_83_; lean_object* v_option_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_option_84_ = l_Lean_Syntax_getArg(v___x_74_, v___x_83_);
lean_dec(v___x_74_);
v___x_85_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__16));
v___x_86_ = l_Lean_mkCIdentFrom(v_v_52_, v___x_85_, v___x_78_);
v___x_87_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_87_, 0, v_v_52_);
lean_ctor_set(v___x_87_, 1, v_option_84_);
lean_ctor_set(v___x_87_, 2, v___x_86_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*3, v___x_62_);
v___y_56_ = v___x_87_;
goto v___jp_55_;
}
}
else
{
lean_object* v___x_88_; lean_object* v_option_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v_option_89_ = l_Lean_Syntax_getArg(v___x_74_, v___x_88_);
lean_dec(v___x_74_);
v___x_90_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18));
v___x_91_ = l_Lean_mkCIdentFrom(v_v_52_, v___x_90_, v___x_76_);
v___x_92_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_92_, 0, v_v_52_);
lean_ctor_set(v___x_92_, 1, v_option_89_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*3, v___x_62_);
v___y_56_ = v___x_92_;
goto v___jp_55_;
}
}
else
{
lean_object* v___x_93_; lean_object* v_option_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v_option_94_ = l_Lean_Syntax_getArg(v___x_74_, v___x_93_);
v___x_95_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__20));
lean_inc(v_option_94_);
v___x_96_ = l_Lean_Syntax_isOfKind(v_option_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_option_94_);
lean_dec(v___x_74_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_98_, 0, v_v_52_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
lean_ctor_set(v___x_98_, 2, v___x_97_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*3, v___x_96_);
v___y_56_ = v___x_98_;
goto v___jp_55_;
}
else
{
lean_object* v___x_99_; lean_object* v_value_100_; uint8_t v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_unsigned_to_nat(3u);
v_value_100_ = l_Lean_Syntax_getArg(v___x_74_, v___x_99_);
lean_dec(v___x_74_);
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_102_, 0, v_v_52_);
lean_ctor_set(v___x_102_, 1, v_option_94_);
lean_ctor_set(v___x_102_, 2, v_value_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*3, v___x_101_);
v___y_56_ = v___x_102_;
goto v___jp_55_;
}
}
}
v___jp_55_:
{
size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_add(v_i_49_, v___x_57_);
v___x_59_ = lean_array_uset(v_bs_x27_54_, v_i_49_, v___y_56_);
v_i_49_ = v___x_58_;
v_bs_50_ = v___x_59_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___boxed(lean_object* v_sz_103_, lean_object* v_i_104_, lean_object* v_bs_105_){
_start:
{
size_t v_sz_boxed_106_; size_t v_i_boxed_107_; lean_object* v_res_108_; 
v_sz_boxed_106_ = lean_unbox_usize(v_sz_103_);
lean_dec(v_sz_103_);
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0(v_sz_boxed_106_, v_i_boxed_107_, v_bs_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object* v_c_109_){
_start:
{
size_t v_sz_110_; size_t v___x_111_; lean_object* v___x_112_; 
v_sz_110_ = lean_array_size(v_c_109_);
v___x_111_ = ((size_t)0ULL);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0(v_sz_110_, v___x_111_, v_c_109_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__1(lean_object* v_msg_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = l_Lean_instInhabitedStructureFieldInfo_default;
v___x_115_ = lean_panic_fn_borrowed(v___x_114_, v_msg_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
return v_x_116_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_head_118_ = lean_ctor_get(v_x_117_, 0);
v_tail_119_ = lean_ctor_get(v_x_117_, 1);
v___x_120_ = l_Lean_Name_getString_x21(v_head_118_);
v___x_121_ = lean_box(0);
v___x_122_ = l_Lean_Name_str___override(v___x_121_, v___x_120_);
v___x_123_ = l_Lean_Name_appendCore(v_x_116_, v___x_122_);
lean_dec(v_x_116_);
v_x_116_ = v___x_123_;
v_x_117_ = v_tail_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0___boxed(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0(v_x_125_, v_x_126_);
lean_dec(v_x_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(lean_object* v_msgData_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_env_135_; uint8_t v___x_136_; lean_object* v_env_137_; lean_object* v___x_138_; lean_object* v_toCold_139_; lean_object* v_mctx_140_; lean_object* v_lctx_141_; lean_object* v_options_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_134_);
v___x_136_ = 0;
v_env_137_ = l_Lean_Environment_setRecordingDeps(v_env_135_, v___x_136_);
v___x_138_ = lean_st_ref_get(v___y_130_);
v_toCold_139_ = lean_ctor_get(v___y_131_, 0);
v_mctx_140_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_mctx_140_);
lean_dec(v___x_138_);
v_lctx_141_ = lean_ctor_get(v___y_129_, 2);
v_options_142_ = lean_ctor_get(v_toCold_139_, 2);
lean_inc_ref(v_options_142_);
lean_inc_ref(v_lctx_141_);
v___x_143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_143_, 0, v_env_137_);
lean_ctor_set(v___x_143_, 1, v_mctx_140_);
lean_ctor_set(v___x_143_, 2, v_lctx_141_);
lean_ctor_set(v___x_143_, 3, v_options_142_);
v___x_144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_msgData_128_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msgData_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 2);
v___x_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_ref_159_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_ref_159_);
lean_ctor_set(v___x_165_, 1, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg___boxed(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__2));
v___x_181_ = lean_unsigned_to_nat(14u);
v___x_182_ = lean_unsigned_to_nat(22u);
v___x_183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__1));
v___x_184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__0));
v___x_185_ = l_mkPanicMessageWithDecl(v___x_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__4));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__6));
v___x_191_ = l_Lean_stringToMessageData(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__8));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__10));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__14));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(lean_object* v_structName_204_, lean_object* v_fieldName_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___x_217_; lean_object* v_env_218_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; uint8_t v___x_252_; 
v___x_217_ = lean_st_ref_get(v_a_209_);
v_env_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_ref_n(v_env_218_, 2);
lean_dec(v___x_217_);
lean_inc(v_structName_204_);
v___x_252_ = l_Lean_isStructure(v_env_218_, v_structName_204_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v_env_218_);
lean_dec(v_fieldName_205_);
v___x_253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_254_ = l_Lean_MessageData_ofConstName(v_structName_204_, v___x_252_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_257_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
v___y_220_ = v_a_206_;
v___y_221_ = v_a_207_;
v___y_222_ = v_a_208_;
v___y_223_ = v_a_209_;
goto v___jp_219_;
}
v___jp_211_:
{
lean_object* v_projFn_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_projFn_214_ = lean_ctor_get(v___y_213_, 1);
lean_inc(v_projFn_214_);
lean_dec_ref(v___y_213_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___y_212_);
lean_ctor_set(v___x_215_, 1, v_projFn_214_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
v___jp_219_:
{
lean_object* v___x_224_; 
lean_inc(v_structName_204_);
lean_inc_ref(v_env_218_);
v___x_224_ = l_Lean_findField_x3f(v_env_218_, v_structName_204_, v_fieldName_205_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_226_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
lean_inc_ref(v_env_218_);
v___x_226_ = l_Lean_getPathToBaseStructure_x3f(v_env_218_, v_val_225_, v_structName_204_);
if (lean_obj_tag(v___x_226_) == 1)
{
lean_object* v_val_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = lean_box(0);
v___x_229_ = l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0(v___x_228_, v_val_227_);
lean_dec(v_val_227_);
lean_inc(v_fieldName_205_);
v___x_230_ = l_Lean_Name_append(v___x_229_, v_fieldName_205_);
v___x_231_ = l_Lean_getFieldInfo_x3f(v_env_218_, v_val_225_, v_fieldName_205_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3);
v___x_233_ = l_panic___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__1(v___x_232_);
v___y_212_ = v___x_230_;
v___y_213_ = v___x_233_;
goto v___jp_211_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_231_, 1);
v___y_212_ = v___x_230_;
v___y_213_ = v_val_234_;
goto v___jp_211_;
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v___x_226_);
lean_dec(v_val_225_);
lean_dec_ref(v_env_218_);
v___x_235_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5);
v___x_236_ = l_Lean_MessageData_ofName(v_fieldName_205_);
v___x_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7);
v___x_239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_239_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_240_;
}
}
else
{
lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v___x_224_);
lean_dec_ref(v_env_218_);
v___x_241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9);
v___x_242_ = 0;
v___x_243_ = l_Lean_MessageData_ofConstName(v_structName_204_, v___x_242_);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_241_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = l_Lean_MessageData_ofName(v_fieldName_205_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_250_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___boxed(lean_object* v_structName_267_, lean_object* v_fieldName_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_267_, v_fieldName_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(lean_object* v_00_u03b1_275_, lean_object* v_msg_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___boxed(lean_object* v_00_u03b1_283_, lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(v_00_u03b1_283_, v_msg_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__0));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__2));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(lean_object* v_fst_297_, lean_object* v_structName_298_, lean_object* v_00_u03b1_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_305_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1);
v___x_306_ = l_Lean_MessageData_ofName(v_fst_297_);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3);
v___x_309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = 0;
v___x_311_ = l_Lean_MessageData_ofConstName(v_structName_298_, v___x_310_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_314_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___boxed(lean_object* v_fst_316_, lean_object* v_structName_317_, lean_object* v_00_u03b1_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_316_, v_structName_317_, v_00_u03b1_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_325_, lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_toCold_332_; lean_object* v_currRecDepth_333_; lean_object* v_ref_334_; uint16_t v_optionFlags_335_; uint8_t v_suppressElabErrors_336_; uint8_t v_isRecordingDeps_337_; lean_object* v_ref_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_toCold_332_ = lean_ctor_get(v___y_329_, 0);
v_currRecDepth_333_ = lean_ctor_get(v___y_329_, 1);
v_ref_334_ = lean_ctor_get(v___y_329_, 2);
v_optionFlags_335_ = lean_ctor_get_uint16(v___y_329_, sizeof(void*)*3);
v_suppressElabErrors_336_ = lean_ctor_get_uint8(v___y_329_, sizeof(void*)*3 + 2);
v_isRecordingDeps_337_ = lean_ctor_get_uint8(v___y_329_, sizeof(void*)*3 + 3);
v_ref_338_ = l_Lean_replaceRef(v_ref_325_, v_ref_334_);
lean_inc(v_currRecDepth_333_);
lean_inc_ref(v_toCold_332_);
v___x_339_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_339_, 0, v_toCold_332_);
lean_ctor_set(v___x_339_, 1, v_currRecDepth_333_);
lean_ctor_set(v___x_339_, 2, v_ref_338_);
lean_ctor_set_uint16(v___x_339_, sizeof(void*)*3, v_optionFlags_335_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*3 + 2, v_suppressElabErrors_336_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*3 + 3, v_isRecordingDeps_337_);
v___x_340_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_326_, v___y_327_, v___y_328_, v___x_339_, v___y_330_);
lean_dec_ref_known(v___x_339_, 3);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_341_, v_msg_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_ref_341_);
return v_res_348_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_349_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
lean_ctor_set(v___x_354_, 3, v___x_353_);
lean_ctor_set(v___x_354_, 4, v___x_352_);
lean_ctor_set(v___x_354_, 5, v___x_352_);
lean_ctor_set(v___x_354_, 6, v___x_352_);
lean_ctor_set(v___x_354_, 7, v___x_352_);
lean_ctor_set(v___x_354_, 8, v___x_352_);
lean_ctor_set(v___x_354_, 9, v___x_352_);
lean_ctor_set(v___x_354_, 10, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_unsigned_to_nat(32u);
v___x_356_ = lean_mk_empty_array_with_capacity(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_358_ = ((size_t)5ULL);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_unsigned_to_nat(32u);
v___x_361_ = lean_mk_empty_array_with_capacity(v___x_360_);
v___x_362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_363_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_359_);
lean_ctor_set(v___x_363_, 3, v___x_359_);
lean_ctor_set_usize(v___x_363_, 4, v___x_358_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_364_ = lean_box(1);
v___x_365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
lean_ctor_set(v___x_367_, 2, v___x_364_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_389_, lean_object* v_declHint_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_env_395_; uint8_t v___x_396_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_st_ref_get(v___y_391_);
v_env_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_env_395_);
lean_dec(v___x_394_);
v___x_396_ = l_Lean_Name_isAnonymous(v_declHint_390_);
if (v___x_396_ == 0)
{
uint8_t v_isExporting_397_; 
v_isExporting_397_ = lean_ctor_get_uint8(v_env_395_, sizeof(void*)*13);
if (v_isExporting_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_env_395_);
lean_dec(v_declHint_390_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_msg_389_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; uint8_t v___x_400_; 
lean_inc_ref(v_env_395_);
v___x_399_ = l_Lean_Environment_setExporting(v_env_395_, v___x_396_);
lean_inc(v_declHint_390_);
lean_inc_ref(v___x_399_);
v___x_400_ = l_Lean_Environment_contains(v___x_399_, v_declHint_390_, v_isExporting_397_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_399_);
lean_dec_ref(v_env_395_);
lean_dec(v_declHint_390_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_msg_389_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_c_407_; lean_object* v___x_408_; 
v___x_402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_403_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_404_ = l_Lean_Options_empty;
v___x_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_405_, 0, v___x_399_);
lean_ctor_set(v___x_405_, 1, v___x_402_);
lean_ctor_set(v___x_405_, 2, v___x_403_);
lean_ctor_set(v___x_405_, 3, v___x_404_);
lean_inc(v_declHint_390_);
v___x_406_ = l_Lean_MessageData_ofConstName(v_declHint_390_, v___x_396_);
v_c_407_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_407_, 0, v___x_405_);
lean_ctor_set(v_c_407_, 1, v___x_406_);
v___x_408_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_395_, v_declHint_390_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v_env_395_);
lean_dec(v_declHint_390_);
v___x_409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_c_407_);
v___x_411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_MessageData_note(v___x_412_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v_msg_389_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_450_; 
v_val_416_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_450_ == 0)
{
v___x_418_ = v___x_408_;
v_isShared_419_ = v_isSharedCheck_450_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v___x_408_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_450_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_mod_422_; uint8_t v___x_423_; 
v___x_420_ = l_Lean_Environment_header(v_env_395_);
lean_dec_ref(v_env_395_);
v___x_421_ = l_Lean_EnvironmentHeader_moduleNames(v___x_420_);
v_mod_422_ = lean_array_get(v___x_393_, v___x_421_, v_val_416_);
lean_dec(v_val_416_);
lean_dec_ref(v___x_421_);
v___x_423_ = l_Lean_isPrivateName(v_declHint_390_);
lean_dec(v_declHint_390_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_424_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_c_407_);
v___x_426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_MessageData_ofName(v_mod_422_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_MessageData_note(v___x_431_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v_msg_389_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
lean_ctor_set(v___x_418_, 0, v___x_433_);
v___x_435_ = v___x_418_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_437_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_c_407_);
v___x_439_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_MessageData_ofName(v_mod_422_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_MessageData_note(v___x_444_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v_msg_389_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
lean_ctor_set(v___x_418_, 0, v___x_446_);
v___x_448_ = v___x_418_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_451_; 
lean_dec_ref(v_env_395_);
lean_dec(v_declHint_390_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_msg_389_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_452_, lean_object* v_declHint_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_452_, v_declHint_453_, v___y_454_);
lean_dec(v___y_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_457_, lean_object* v_declHint_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v___x_464_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_457_, v_declHint_458_, v___y_462_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = l_Lean_unknownIdentifierMessageTag;
v___x_470_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_a_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_475_, lean_object* v_declHint_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_475_, v_declHint_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_483_, lean_object* v_msg_484_, lean_object* v_declHint_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_a_492_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_484_, v_declHint_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_491_);
v___x_493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_483_, v_a_492_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_494_, lean_object* v_msg_495_, lean_object* v_declHint_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_494_, v_msg_495_, v_declHint_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v_ref_494_);
return v_res_502_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_506_, lean_object* v_constName_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_513_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_514_ = 0;
lean_inc(v_constName_507_);
v___x_515_ = l_Lean_MessageData_ofConstName(v_constName_507_, v___x_514_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_506_, v___x_518_, v_constName_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_520_, lean_object* v_constName_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_520_, v_constName_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v_ref_520_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(lean_object* v_constName_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_ref_534_; lean_object* v___x_535_; 
v_ref_534_ = lean_ctor_get(v___y_531_, 2);
v___x_535_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_534_, v_constName_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg___boxed(lean_object* v_constName_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(lean_object* v_constName_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; lean_object* v_env_550_; uint8_t v___x_551_; lean_object* v___x_552_; 
v___x_549_ = lean_st_ref_get(v___y_547_);
v_env_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_env_550_);
lean_dec(v___x_549_);
v___x_551_ = 0;
lean_inc(v_constName_543_);
v___x_552_ = l_Lean_Environment_find_x3f(v_env_550_, v_constName_543_, v___x_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_553_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_constName_543_);
v_val_554_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_val_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0___boxed(lean_object* v_constName_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_constName_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_568_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(lean_object* v_structName_572_, lean_object* v_field_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
if (lean_obj_tag(v_field_573_) == 1)
{
lean_object* v_pre_579_; 
v_pre_579_ = lean_ctor_get(v_field_573_, 0);
if (lean_obj_tag(v_pre_579_) == 0)
{
lean_object* v_str_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_str_580_ = lean_ctor_get(v_field_573_, 1);
lean_inc_ref(v_str_580_);
lean_dec_ref_known(v_field_573_, 2);
v___x_581_ = lean_box(0);
v___x_582_ = l_Lean_Name_str___override(v___x_581_, v_str_580_);
v___x_583_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_572_, v___x_582_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
return v___x_583_;
}
else
{
lean_object* v_str_584_; lean_object* v___x_585_; 
lean_inc(v_pre_579_);
v_str_584_ = lean_ctor_get(v_field_573_, 1);
lean_inc_ref(v_str_584_);
lean_dec_ref_known(v_field_573_, 2);
lean_inc(v_structName_572_);
v___x_585_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_572_, v_pre_579_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v_fst_587_ = lean_ctor_get(v_a_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_a_586_, 1);
lean_inc(v_snd_588_);
lean_dec(v_a_586_);
v___x_589_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_snd_588_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = l_Lean_ConstantInfo_type(v_a_590_);
lean_dec(v_a_590_);
v___x_592_ = l_Lean_Expr_getForallBody(v___x_591_);
lean_dec_ref(v___x_591_);
if (lean_obj_tag(v___x_592_) == 4)
{
lean_object* v_declName_593_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___x_620_; lean_object* v_env_621_; uint8_t v___x_622_; 
v_declName_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_n(v_declName_593_, 2);
lean_dec_ref_known(v___x_592_, 2);
v___x_620_ = lean_st_ref_get(v_a_577_);
v_env_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_620_);
v___x_622_ = l_Lean_isStructure(v_env_621_, v_declName_593_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_inc(v_fst_587_);
v___x_623_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_587_, v_structName_572_, lean_box(0), v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_dec_ref_known(v___x_623_, 1);
v___y_595_ = v_a_574_;
v___y_596_ = v_a_575_;
v___y_597_ = v_a_576_;
v___y_598_ = v_a_577_;
goto v___jp_594_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_declName_593_);
lean_dec(v_fst_587_);
lean_dec_ref(v_str_584_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_dec(v_structName_572_);
v___y_595_ = v_a_574_;
v___y_596_ = v_a_575_;
v___y_597_ = v_a_576_;
v___y_598_ = v_a_577_;
goto v___jp_594_;
}
v___jp_594_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = l_Lean_Name_str___override(v___x_599_, v_str_584_);
v___x_601_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_declName_593_, v___x_600_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_619_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_619_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_619_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_619_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_618_; 
v_fst_606_ = lean_ctor_get(v_a_602_, 0);
v_snd_607_ = lean_ctor_get(v_a_602_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_609_ = v_a_602_;
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
lean_dec(v_a_602_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = l_Lean_Name_append(v_fst_587_, v_fst_606_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_snd_607_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_613_);
v___x_615_ = v___x_604_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_dec(v_fst_587_);
return v___x_601_;
}
}
}
else
{
lean_object* v___x_632_; 
lean_dec_ref(v___x_592_);
lean_dec_ref(v_str_584_);
v___x_632_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_587_, v_structName_572_, lean_box(0), v_a_574_, v_a_575_, v_a_576_, v_a_577_);
return v___x_632_;
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_fst_587_);
lean_dec_ref(v_str_584_);
lean_dec(v_structName_572_);
v_a_633_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_589_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_589_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_dec_ref(v_str_584_);
lean_dec(v_structName_572_);
return v___x_585_;
}
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_field_573_);
lean_dec(v_structName_572_);
v___x_641_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1);
v___x_642_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_641_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___boxed(lean_object* v_structName_643_, lean_object* v_field_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_643_, v_field_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(lean_object* v_00_u03b1_651_, lean_object* v_constName_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___boxed(lean_object* v_00_u03b1_659_, lean_object* v_constName_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(v_00_u03b1_659_, v_constName_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_667_, lean_object* v_ref_668_, lean_object* v_constName_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_668_, v_constName_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_676_, lean_object* v_ref_677_, lean_object* v_constName_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(v_00_u03b1_676_, v_ref_677_, v_constName_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v_ref_677_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_685_, lean_object* v_ref_686_, lean_object* v_msg_687_, lean_object* v_declHint_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_686_, v_msg_687_, v_declHint_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_695_, lean_object* v_ref_696_, lean_object* v_msg_697_, lean_object* v_declHint_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_695_, v_ref_696_, v_msg_697_, v_declHint_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v_ref_696_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_705_, lean_object* v_declHint_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_705_, v_declHint_706_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_713_, lean_object* v_declHint_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_713_, v_declHint_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_721_, lean_object* v_ref_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_722_, v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_730_, lean_object* v_ref_731_, lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_730_, v_ref_731_, v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v_ref_731_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(lean_object* v_e_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = l_Lean_Expr_hasMVar(v_e_739_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_e_739_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v_mctx_745_; lean_object* v___x_746_; lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_749_; lean_object* v_cache_750_; lean_object* v_zetaDeltaFVarIds_751_; lean_object* v_postponed_752_; lean_object* v_diag_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_762_; 
v___x_744_ = lean_st_ref_get(v___y_740_);
v_mctx_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_mctx_745_);
lean_dec(v___x_744_);
v___x_746_ = l_Lean_instantiateMVarsCore(v_mctx_745_, v_e_739_);
v_fst_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_fst_747_);
v_snd_748_ = lean_ctor_get(v___x_746_, 1);
lean_inc(v_snd_748_);
lean_dec_ref(v___x_746_);
v___x_749_ = lean_st_ref_take(v___y_740_);
v_cache_750_ = lean_ctor_get(v___x_749_, 1);
v_zetaDeltaFVarIds_751_ = lean_ctor_get(v___x_749_, 2);
v_postponed_752_ = lean_ctor_get(v___x_749_, 3);
v_diag_753_ = lean_ctor_get(v___x_749_, 4);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_763_);
v___x_755_ = v___x_749_;
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_diag_753_);
lean_inc(v_postponed_752_);
lean_inc(v_zetaDeltaFVarIds_751_);
lean_inc(v_cache_750_);
lean_dec(v___x_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_snd_748_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_snd_748_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_cache_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_zetaDeltaFVarIds_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_postponed_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_diag_753_);
v___x_758_ = v_reuseFailAlloc_761_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_st_ref_put(v___y_740_, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_fst_747_);
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg___boxed(lean_object* v_e_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_764_, v___y_765_);
lean_dec(v___y_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(lean_object* v_e_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_768_, v___y_772_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___boxed(lean_object* v_e_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(v_e_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
v___x_794_ = lean_apply_7(v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, lean_box(0));
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed(lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(v_x_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(lean_object* v_lctx_804_, lean_object* v_localInsts_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___f_814_; lean_object* v___x_815_; 
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
v___f_814_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_814_, 0, v_x_806_);
lean_closure_set(v___f_814_, 1, v___y_807_);
lean_closure_set(v___f_814_, 2, v___y_808_);
v___x_815_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_804_, v_localInsts_805_, v___f_814_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_815_) == 0)
{
return v___x_815_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___boxed(lean_object* v_lctx_824_, lean_object* v_localInsts_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_824_, v_localInsts_825_, v_x_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(lean_object* v_00_u03b1_835_, lean_object* v_lctx_836_, lean_object* v_localInsts_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_836_, v_localInsts_837_, v_x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed(lean_object* v_00_u03b1_847_, lean_object* v_lctx_848_, lean_object* v_localInsts_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(v_00_u03b1_847_, v_lctx_848_, v_localInsts_849_, v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl(lean_box(0), v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_867_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg___boxed(lean_object* v_x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(lean_object* v_00_u03b1_893_, lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___boxed(lean_object* v_00_u03b1_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(v_00_u03b1_903_, v_x_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_912_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Array_mkArray0___redArg();
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(lean_object* v_structName_941_, lean_object* v_source_x3f_942_, lean_object* v_fields_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
if (lean_obj_tag(v_source_x3f_942_) == 0)
{
lean_object* v_ref_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_ref_951_ = lean_ctor_get(v___y_948_, 2);
v___x_952_ = 0;
v___x_953_ = l_Lean_SourceInfo_fromRef(v_ref_951_, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_953_, 8);
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_953_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_958_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_959_, 0, v___x_953_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_962_ = l_Lean_Syntax_SepArray_ofElems(v___x_961_, v_fields_943_);
v___x_963_ = l_Array_append___redArg(v___x_958_, v___x_962_);
lean_dec_ref(v___x_962_);
v___x_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_953_);
lean_ctor_set(v___x_964_, 1, v___x_957_);
lean_ctor_set(v___x_964_, 2, v___x_963_);
v___x_965_ = l_Lean_Syntax_node1(v___x_953_, v___x_960_, v___x_964_);
v___x_966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_959_);
v___x_967_ = l_Lean_Syntax_node1(v___x_953_, v___x_966_, v___x_959_);
v___x_968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_953_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_mkCIdent(v_structName_941_);
v___x_971_ = l_Lean_Syntax_node2(v___x_953_, v___x_957_, v___x_969_, v___x_970_);
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_953_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_Syntax_node6(v___x_953_, v___x_954_, v___x_956_, v___x_959_, v___x_965_, v___x_967_, v___x_971_, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
else
{
lean_object* v_val_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1011_; 
v_val_976_ = lean_ctor_get(v_source_x3f_942_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_source_x3f_942_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_978_ = v_source_x3f_942_;
v_isShared_979_ = v_isSharedCheck_1011_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_val_976_);
lean_dec(v_source_x3f_942_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1011_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_ref_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v_ref_980_ = lean_ctor_get(v___y_948_, 2);
v___x_981_ = 0;
v___x_982_ = l_Lean_SourceInfo_fromRef(v_ref_980_, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_982_, 11);
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_982_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_987_ = l_Lean_Syntax_node1(v___x_982_, v___x_986_, v_val_976_);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_982_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_Syntax_node2(v___x_982_, v___x_986_, v___x_987_, v___x_989_);
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_994_ = l_Lean_Syntax_SepArray_ofElems(v___x_993_, v_fields_943_);
v___x_995_ = l_Array_append___redArg(v___x_992_, v___x_994_);
lean_dec_ref(v___x_994_);
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v___x_982_);
lean_ctor_set(v___x_996_, 1, v___x_986_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
v___x_997_ = l_Lean_Syntax_node1(v___x_982_, v___x_991_, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_982_);
lean_ctor_set(v___x_999_, 1, v___x_986_);
lean_ctor_set(v___x_999_, 2, v___x_992_);
v___x_1000_ = l_Lean_Syntax_node1(v___x_982_, v___x_998_, v___x_999_);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_982_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_mkCIdent(v_structName_941_);
v___x_1004_ = l_Lean_Syntax_node2(v___x_982_, v___x_986_, v___x_1002_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_982_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node6(v___x_982_, v___x_983_, v___x_985_, v___x_990_, v___x_997_, v___x_1000_, v___x_1004_, v___x_1006_);
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 0);
lean_ctor_set(v___x_978_, 0, v___x_1007_);
v___x_1009_ = v___x_978_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed(lean_object* v_structName_1012_, lean_object* v_source_x3f_1013_, lean_object* v_fields_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_1012_, v_source_x3f_1013_, v_fields_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_fields_1014_);
return v_res_1022_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_1040_ = l_String_toRawSubstring_x27(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(lean_object* v_a_1090_, lean_object* v_structName_1091_, lean_object* v_____r_1092_, lean_object* v_source_x3f_1093_, lean_object* v_seenFields_1094_, lean_object* v_fields_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_toCold_1103_; lean_object* v_value_1104_; lean_object* v_ref_1105_; lean_object* v_quotContext_1106_; lean_object* v_currMacroScope_1107_; lean_object* v_ref_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_toCold_1103_ = lean_ctor_get(v___y_1100_, 0);
v_value_1104_ = lean_ctor_get(v_a_1090_, 2);
lean_inc(v_value_1104_);
lean_dec_ref(v_a_1090_);
v_ref_1105_ = lean_ctor_get(v___y_1100_, 2);
v_quotContext_1106_ = lean_ctor_get(v_toCold_1103_, 8);
v_currMacroScope_1107_ = lean_ctor_get(v_toCold_1103_, 9);
v_ref_1108_ = l_Lean_replaceRef(v_value_1104_, v_ref_1105_);
v___x_1109_ = 0;
v___x_1110_ = l_Lean_SourceInfo_fromRef(v_ref_1108_, v___x_1109_);
lean_dec(v_ref_1108_);
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1));
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_1110_, 8);
v___x_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1110_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_1116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_1117_ = lean_box(0);
lean_inc(v_currMacroScope_1107_);
lean_inc(v_quotContext_1106_);
v___x_1118_ = l_Lean_addMacroScope(v_quotContext_1106_, v___x_1117_, v_currMacroScope_1107_);
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_1120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1110_);
lean_ctor_set(v___x_1120_, 1, v___x_1116_);
lean_ctor_set(v___x_1120_, 2, v___x_1118_);
lean_ctor_set(v___x_1120_, 3, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node1(v___x_1110_, v___x_1115_, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node2(v___x_1110_, v___x_1112_, v___x_1114_, v___x_1121_);
v___x_1123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1110_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_1126_ = l_Lean_mkCIdent(v_structName_1091_);
lean_inc(v___x_1126_);
v___x_1127_ = l_Lean_Syntax_node1(v___x_1110_, v___x_1125_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_1129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1110_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
lean_inc_ref(v___x_1124_);
v___x_1130_ = l_Lean_Syntax_node5(v___x_1110_, v___x_1111_, v___x_1122_, v_value_1104_, v___x_1124_, v___x_1127_, v___x_1129_);
if (lean_obj_tag(v_source_x3f_1093_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1162_; 
v_val_1131_ = lean_ctor_get(v_source_x3f_1093_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_source_x3f_1093_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1133_ = v_source_x3f_1093_;
v_isShared_1134_ = v_isSharedCheck_1162_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v_source_x3f_1093_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1162_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_1110_, 10);
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1110_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1110_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_Syntax_node3(v___x_1110_, v___x_1125_, v___x_1130_, v___x_1139_, v_val_1131_);
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1110_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_Syntax_node2(v___x_1110_, v___x_1125_, v___x_1140_, v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_1145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1110_);
lean_ctor_set(v___x_1146_, 1, v___x_1125_);
lean_ctor_set(v___x_1146_, 2, v___x_1145_);
lean_inc_ref(v___x_1146_);
v___x_1147_ = l_Lean_Syntax_node1(v___x_1110_, v___x_1144_, v___x_1146_);
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1149_ = l_Lean_Syntax_node1(v___x_1110_, v___x_1148_, v___x_1146_);
v___x_1150_ = l_Lean_Syntax_node2(v___x_1110_, v___x_1125_, v___x_1124_, v___x_1126_);
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1110_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_Syntax_node6(v___x_1110_, v___x_1135_, v___x_1137_, v___x_1143_, v___x_1147_, v___x_1149_, v___x_1150_, v___x_1152_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1153_);
v___x_1155_ = v___x_1133_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_seenFields_1094_);
lean_ctor_set(v___x_1157_, 1, v_fields_1095_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1156_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v___x_1126_);
lean_dec_ref_known(v___x_1124_, 2);
lean_dec(v___x_1110_);
lean_dec(v_source_x3f_1093_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1130_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_seenFields_1094_);
lean_ctor_set(v___x_1165_, 1, v_fields_1095_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1163_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1164_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___boxed(lean_object* v_a_1169_, lean_object* v_structName_1170_, lean_object* v_____r_1171_, lean_object* v_source_x3f_1172_, lean_object* v_seenFields_1173_, lean_object* v_fields_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_1169_, v_structName_1170_, v_____r_1171_, v_source_x3f_1172_, v_seenFields_1173_, v_fields_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(lean_object* v_opts_1183_, lean_object* v_opt_1184_){
_start:
{
lean_object* v_name_1185_; lean_object* v_defValue_1186_; lean_object* v_map_1187_; lean_object* v___x_1188_; 
v_name_1185_ = lean_ctor_get(v_opt_1184_, 0);
v_defValue_1186_ = lean_ctor_get(v_opt_1184_, 1);
v_map_1187_ = lean_ctor_get(v_opts_1183_, 0);
v___x_1188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1187_, v_name_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_unbox(v_defValue_1186_);
return v___x_1189_;
}
else
{
lean_object* v_val_1190_; 
v_val_1190_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v___x_1188_, 1);
if (lean_obj_tag(v_val_1190_) == 1)
{
uint8_t v_v_1191_; 
v_v_1191_ = lean_ctor_get_uint8(v_val_1190_, 0);
lean_dec_ref_known(v_val_1190_, 0);
return v_v_1191_;
}
else
{
uint8_t v___x_1192_; 
lean_dec(v_val_1190_);
v___x_1192_ = lean_unbox(v_defValue_1186_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_opts_1193_, lean_object* v_opt_1194_){
_start:
{
uint8_t v_res_1195_; lean_object* v_r_1196_; 
v_res_1195_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_opts_1193_, v_opt_1194_);
lean_dec_ref(v_opt_1194_);
lean_dec_ref(v_opts_1193_);
v_r_1196_ = lean_box(v_res_1195_);
return v_r_1196_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(1);
v___x_1198_ = l_Lean_MessageData_ofFormat(v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2));
v___x_1203_ = l_Lean_MessageData_ofFormat(v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(lean_object* v_x_1204_, lean_object* v_x_1205_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
return v_x_1204_;
}
else
{
lean_object* v_head_1206_; lean_object* v_tail_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1229_; 
v_head_1206_ = lean_ctor_get(v_x_1205_, 0);
v_tail_1207_ = lean_ctor_get(v_x_1205_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x_1205_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1209_ = v_x_1205_;
v_isShared_1210_ = v_isSharedCheck_1229_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_tail_1207_);
lean_inc(v_head_1206_);
lean_dec(v_x_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1229_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_before_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1227_; 
v_before_1211_ = lean_ctor_get(v_head_1206_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_head_1206_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v_head_1206_, 1);
lean_dec(v_unused_1228_);
v___x_1213_ = v_head_1206_;
v_isShared_1214_ = v_isSharedCheck_1227_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_before_1211_);
lean_dec(v_head_1206_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1227_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 7);
lean_ctor_set(v___x_1213_, 1, v___x_1215_);
lean_ctor_set(v___x_1213_, 0, v_x_1204_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_x_1204_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 7);
lean_ctor_set(v___x_1209_, 1, v___x_1218_);
lean_ctor_set(v___x_1209_, 0, v___x_1217_);
v___x_1220_ = v___x_1209_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = l_Lean_MessageData_ofSyntax(v_before_1211_);
v___x_1222_ = l_Lean_indentD(v___x_1221_);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1220_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v_x_1204_ = v___x_1223_;
v_x_1205_ = v_tail_1207_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1));
v___x_1234_ = l_Lean_MessageData_ofFormat(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(lean_object* v_msgData_1235_, lean_object* v_macroStack_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1237_);
v___x_1240_ = l_Lean_Elab_pp_macroStack;
v___x_1241_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v___x_1239_, v___x_1240_);
lean_dec_ref(v___x_1239_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_dec(v_macroStack_1236_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_msgData_1235_);
return v___x_1242_;
}
else
{
if (lean_obj_tag(v_macroStack_1236_) == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_msgData_1235_);
return v___x_1243_;
}
else
{
lean_object* v_head_1244_; lean_object* v_after_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1260_; 
v_head_1244_ = lean_ctor_get(v_macroStack_1236_, 0);
lean_inc(v_head_1244_);
v_after_1245_ = lean_ctor_get(v_head_1244_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_head_1244_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_head_1244_, 0);
lean_dec(v_unused_1261_);
v___x_1247_ = v_head_1244_;
v_isShared_1248_ = v_isSharedCheck_1260_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_after_1245_);
lean_dec(v_head_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1260_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 7);
lean_ctor_set(v___x_1247_, 1, v___x_1249_);
lean_ctor_set(v___x_1247_, 0, v_msgData_1235_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_msgData_1235_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_msgData_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1252_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = l_Lean_MessageData_ofSyntax(v_after_1245_);
v___x_1255_ = l_Lean_indentD(v___x_1254_);
v_msgData_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1256_, 0, v___x_1253_);
lean_ctor_set(v_msgData_1256_, 1, v___x_1255_);
v___x_1257_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(v_msgData_1256_, v_macroStack_1236_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___boxed(lean_object* v_msgData_1262_, lean_object* v_macroStack_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_1262_, v_macroStack_1263_, v___y_1264_);
lean_dec_ref(v___y_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(lean_object* v_msg_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_ref_1275_; lean_object* v_macroStack_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_ref_1275_ = lean_ctor_get(v___y_1272_, 2);
v_macroStack_1276_ = lean_ctor_get(v___y_1268_, 1);
v___x_1277_ = l_Lean_Elab_getBetterRef(v_ref_1275_, v_macroStack_1276_);
v___x_1278_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_1267_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
lean_inc(v_macroStack_1276_);
v___x_1280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_a_1279_, v_macroStack_1276_, v___y_1272_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1277_);
lean_ctor_set(v___x_1285_, 1, v_a_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 1);
lean_ctor_set(v___x_1283_, 0, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg___boxed(lean_object* v_msg_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(lean_object* v_ref_1299_, lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_toCold_1308_; lean_object* v_currRecDepth_1309_; lean_object* v_ref_1310_; uint16_t v_optionFlags_1311_; uint8_t v_suppressElabErrors_1312_; uint8_t v_isRecordingDeps_1313_; lean_object* v_ref_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_toCold_1308_ = lean_ctor_get(v___y_1305_, 0);
v_currRecDepth_1309_ = lean_ctor_get(v___y_1305_, 1);
v_ref_1310_ = lean_ctor_get(v___y_1305_, 2);
v_optionFlags_1311_ = lean_ctor_get_uint16(v___y_1305_, sizeof(void*)*3);
v_suppressElabErrors_1312_ = lean_ctor_get_uint8(v___y_1305_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1313_ = lean_ctor_get_uint8(v___y_1305_, sizeof(void*)*3 + 3);
v_ref_1314_ = l_Lean_replaceRef(v_ref_1299_, v_ref_1310_);
lean_inc(v_currRecDepth_1309_);
lean_inc_ref(v_toCold_1308_);
v___x_1315_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1315_, 0, v_toCold_1308_);
lean_ctor_set(v___x_1315_, 1, v_currRecDepth_1309_);
lean_ctor_set(v___x_1315_, 2, v_ref_1314_);
lean_ctor_set_uint16(v___x_1315_, sizeof(void*)*3, v_optionFlags_1311_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*3 + 2, v_suppressElabErrors_1312_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*3 + 3, v_isRecordingDeps_1313_);
v___x_1316_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___x_1315_, v___y_1306_);
lean_dec_ref_known(v___x_1315_, 3);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg___boxed(lean_object* v_ref_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1317_, v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v_ref_1317_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(lean_object* v_msg_1327_, lean_object* v_declHint_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_env_1333_; uint8_t v___x_1334_; 
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_st_ref_get(v___y_1329_);
v_env_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_ref(v_env_1333_);
lean_dec(v___x_1332_);
v___x_1334_ = l_Lean_Name_isAnonymous(v_declHint_1328_);
if (v___x_1334_ == 0)
{
uint8_t v_isExporting_1335_; 
v_isExporting_1335_ = lean_ctor_get_uint8(v_env_1333_, sizeof(void*)*13);
if (v_isExporting_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v_env_1333_);
lean_dec(v_declHint_1328_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_msg_1327_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
lean_inc_ref(v_env_1333_);
v___x_1337_ = l_Lean_Environment_setExporting(v_env_1333_, v___x_1334_);
lean_inc(v_declHint_1328_);
lean_inc_ref(v___x_1337_);
v___x_1338_ = l_Lean_Environment_contains(v___x_1337_, v_declHint_1328_, v_isExporting_1335_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_env_1333_);
lean_dec(v_declHint_1328_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_msg_1327_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v_c_1347_; lean_object* v___x_1348_; 
v___x_1340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1341_ = lean_unsigned_to_nat(32u);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1341_);
lean_dec_ref(v___x_1342_);
v___x_1343_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1344_ = l_Lean_Options_empty;
v___x_1345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1337_);
lean_ctor_set(v___x_1345_, 1, v___x_1340_);
lean_ctor_set(v___x_1345_, 2, v___x_1343_);
lean_ctor_set(v___x_1345_, 3, v___x_1344_);
lean_inc(v_declHint_1328_);
v___x_1346_ = l_Lean_MessageData_ofConstName(v_declHint_1328_, v___x_1334_);
v_c_1347_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1347_, 0, v___x_1345_);
lean_ctor_set(v_c_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1333_, v_declHint_1328_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec_ref(v_env_1333_);
lean_dec(v_declHint_1328_);
v___x_1349_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_c_1347_);
v___x_1351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_MessageData_note(v___x_1352_);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_msg_1327_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1390_; 
v_val_1356_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1358_ = v___x_1348_;
v_isShared_1359_ = v_isSharedCheck_1390_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_val_1356_);
lean_dec(v___x_1348_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1390_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_mod_1362_; uint8_t v___x_1363_; 
v___x_1360_ = l_Lean_Environment_header(v_env_1333_);
lean_dec_ref(v_env_1333_);
v___x_1361_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1360_);
v_mod_1362_ = lean_array_get(v___x_1331_, v___x_1361_, v_val_1356_);
lean_dec(v_val_1356_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = l_Lean_isPrivateName(v_declHint_1328_);
lean_dec(v_declHint_1328_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v_c_1347_);
v___x_1366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_MessageData_ofName(v_mod_1362_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_MessageData_note(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_msg_1327_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1373_);
v___x_1375_ = v___x_1358_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1377_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_c_1347_);
v___x_1379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_ofName(v_mod_1362_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_Lean_MessageData_note(v___x_1384_);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_msg_1327_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1386_);
v___x_1388_ = v___x_1358_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1391_; 
lean_dec_ref(v_env_1333_);
lean_dec(v_declHint_1328_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_msg_1327_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg___boxed(lean_object* v_msg_1392_, lean_object* v_declHint_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1392_, v_declHint_1393_, v___y_1394_);
lean_dec(v___y_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(lean_object* v_msg_1397_, lean_object* v_declHint_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1416_; 
v___x_1406_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1397_, v_declHint_1398_, v___y_1404_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1416_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1416_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1411_ = l_Lean_unknownIdentifierMessageTag;
v___x_1412_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_a_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1412_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23___boxed(lean_object* v_msg_1417_, lean_object* v_declHint_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1417_, v_declHint_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(lean_object* v_ref_1427_, lean_object* v_msg_1428_, lean_object* v_declHint_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1428_, v_declHint_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1427_, v_a_1438_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg___boxed(lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v_declHint_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1440_, v_msg_1441_, v_declHint_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v_ref_1440_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(lean_object* v_ref_1451_, lean_object* v_constName_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1460_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1461_ = 0;
lean_inc(v_constName_1452_);
v___x_1462_ = l_Lean_MessageData_ofConstName(v_constName_1452_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1460_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1451_, v___x_1465_, v_constName_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_ref_1467_, lean_object* v_constName_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1467_, v_constName_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v_ref_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(lean_object* v_constName_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_ref_1485_; lean_object* v___x_1486_; 
v_ref_1485_ = lean_ctor_get(v___y_1482_, 2);
v___x_1486_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1485_, v_constName_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg___boxed(lean_object* v_constName_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(lean_object* v_constName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v_env_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1504_ = lean_st_ref_get(v___y_1502_);
v_env_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc_ref(v_env_1505_);
lean_dec(v___x_1504_);
v___x_1506_ = 0;
lean_inc(v_constName_1496_);
v___x_1507_ = l_Lean_Environment_find_x3f(v_env_1505_, v_constName_1496_, v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1508_;
}
else
{
lean_object* v_val_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_constName_1496_);
v_val_1509_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1507_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_val_1509_);
lean_dec(v___x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 0);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_val_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2___boxed(lean_object* v_constName_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_constName_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1525_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(uint8_t v_suppressElabErrors_1532_, uint8_t v___y_1533_, lean_object* v_x_1534_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 1)
{
lean_object* v_pre_1535_; 
v_pre_1535_ = lean_ctor_get(v_x_1534_, 0);
switch(lean_obj_tag(v_pre_1535_))
{
case 1:
{
lean_object* v_pre_1536_; 
v_pre_1536_ = lean_ctor_get(v_pre_1535_, 0);
switch(lean_obj_tag(v_pre_1536_))
{
case 0:
{
lean_object* v_str_1537_; lean_object* v_str_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_str_1537_ = lean_ctor_get(v_x_1534_, 1);
v_str_1538_ = lean_ctor_get(v_pre_1535_, 1);
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8));
v___x_1540_ = lean_string_dec_eq(v_str_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2));
v___x_1542_ = lean_string_dec_eq(v_str_1538_, v___x_1541_);
if (v___x_1542_ == 0)
{
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___x_1544_ = lean_string_dec_eq(v_str_1537_, v___x_1543_);
if (v___x_1544_ == 0)
{
return v___x_1544_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
}
else
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1));
v___x_1546_ = lean_string_dec_eq(v_str_1537_, v___x_1545_);
if (v___x_1546_ == 0)
{
return v___x_1546_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
}
case 1:
{
lean_object* v_pre_1547_; 
v_pre_1547_ = lean_ctor_get(v_pre_1536_, 0);
if (lean_obj_tag(v_pre_1547_) == 0)
{
lean_object* v_str_1548_; lean_object* v_str_1549_; lean_object* v_str_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_str_1548_ = lean_ctor_get(v_x_1534_, 1);
v_str_1549_ = lean_ctor_get(v_pre_1535_, 1);
v_str_1550_ = lean_ctor_get(v_pre_1536_, 1);
v___x_1551_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2));
v___x_1552_ = lean_string_dec_eq(v_str_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3));
v___x_1554_ = lean_string_dec_eq(v_str_1549_, v___x_1553_);
if (v___x_1554_ == 0)
{
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4));
v___x_1556_ = lean_string_dec_eq(v_str_1548_, v___x_1555_);
if (v___x_1556_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
}
}
else
{
return v___y_1533_;
}
}
default: 
{
return v___y_1533_;
}
}
}
case 0:
{
lean_object* v_str_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_str_1557_ = lean_ctor_get(v_x_1534_, 1);
v___x_1558_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5));
v___x_1559_ = lean_string_dec_eq(v_str_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
return v___x_1559_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
default: 
{
return v___y_1533_;
}
}
}
else
{
return v___y_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1560_, lean_object* v___y_1561_, lean_object* v_x_1562_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1563_; uint8_t v___y_49465__boxed_1564_; uint8_t v_res_1565_; lean_object* v_r_1566_; 
v_suppressElabErrors_boxed_1563_ = lean_unbox(v_suppressElabErrors_1560_);
v___y_49465__boxed_1564_ = lean_unbox(v___y_1561_);
v_res_1565_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(v_suppressElabErrors_boxed_1563_, v___y_49465__boxed_1564_, v_x_1562_);
lean_dec(v_x_1562_);
v_r_1566_ = lean_box(v_res_1565_);
return v_r_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1567_, lean_object* v_msgData_1568_, uint8_t v_severity_1569_, uint8_t v_isSilent_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___y_1577_; uint8_t v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v_toCold_1584_; lean_object* v___y_1585_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; uint8_t v___y_1617_; uint8_t v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1641_; uint8_t v___y_1642_; lean_object* v___y_1643_; uint8_t v___y_1644_; uint8_t v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; uint8_t v___y_1651_; uint8_t v___y_1652_; uint8_t v___y_1653_; uint8_t v___x_1664_; uint8_t v___y_1666_; uint8_t v___y_1667_; uint8_t v___y_1668_; uint8_t v___y_1670_; uint8_t v___x_1678_; 
v___x_1664_ = 2;
v___x_1678_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1569_, v___x_1664_);
if (v___x_1678_ == 0)
{
v___y_1670_ = v___x_1678_;
goto v___jp_1669_;
}
else
{
uint8_t v___x_1679_; 
lean_inc_ref(v_msgData_1568_);
v___x_1679_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1568_);
v___y_1670_ = v___x_1679_;
goto v___jp_1669_;
}
v___jp_1576_:
{
lean_object* v_currNamespace_1586_; lean_object* v_openDecls_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v_env_1592_; lean_object* v_nextMacroScope_1593_; lean_object* v_ngen_1594_; lean_object* v_auxDeclNGen_1595_; lean_object* v_traceState_1596_; lean_object* v_cache_1597_; lean_object* v_recordedDeps_1598_; lean_object* v_messages_1599_; lean_object* v_infoState_1600_; lean_object* v_snapshotTasks_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1612_; 
v_currNamespace_1586_ = lean_ctor_get(v_toCold_1584_, 4);
v_openDecls_1587_ = lean_ctor_get(v_toCold_1584_, 5);
lean_inc(v_openDecls_1587_);
lean_inc(v_currNamespace_1586_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_currNamespace_1586_);
lean_ctor_set(v___x_1588_, 1, v_openDecls_1587_);
v___x_1589_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___y_1581_);
lean_inc_ref(v___y_1582_);
lean_inc_ref(v___y_1583_);
v___x_1590_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1590_, 0, v___y_1583_);
lean_ctor_set(v___x_1590_, 1, v___y_1579_);
lean_ctor_set(v___x_1590_, 2, v___y_1577_);
lean_ctor_set(v___x_1590_, 3, v___y_1582_);
lean_ctor_set(v___x_1590_, 4, v___x_1589_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*5, v___y_1578_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*5 + 1, v___y_1580_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*5 + 2, v_isSilent_1570_);
v___x_1591_ = lean_st_ref_take(v___y_1585_);
v_env_1592_ = lean_ctor_get(v___x_1591_, 0);
v_nextMacroScope_1593_ = lean_ctor_get(v___x_1591_, 1);
v_ngen_1594_ = lean_ctor_get(v___x_1591_, 2);
v_auxDeclNGen_1595_ = lean_ctor_get(v___x_1591_, 3);
v_traceState_1596_ = lean_ctor_get(v___x_1591_, 4);
v_cache_1597_ = lean_ctor_get(v___x_1591_, 5);
v_recordedDeps_1598_ = lean_ctor_get(v___x_1591_, 6);
v_messages_1599_ = lean_ctor_get(v___x_1591_, 7);
v_infoState_1600_ = lean_ctor_get(v___x_1591_, 8);
v_snapshotTasks_1601_ = lean_ctor_get(v___x_1591_, 9);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1603_ = v___x_1591_;
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snapshotTasks_1601_);
lean_inc(v_infoState_1600_);
lean_inc(v_messages_1599_);
lean_inc(v_recordedDeps_1598_);
lean_inc(v_cache_1597_);
lean_inc(v_traceState_1596_);
lean_inc(v_auxDeclNGen_1595_);
lean_inc(v_ngen_1594_);
lean_inc(v_nextMacroScope_1593_);
lean_inc(v_env_1592_);
lean_dec(v___x_1591_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = l_Lean_MessageLog_add(v___x_1590_, v_messages_1599_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 7, v___x_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_env_1592_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_nextMacroScope_1593_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_ngen_1594_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_auxDeclNGen_1595_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_traceState_1596_);
lean_ctor_set(v_reuseFailAlloc_1611_, 5, v_cache_1597_);
lean_ctor_set(v_reuseFailAlloc_1611_, 6, v_recordedDeps_1598_);
lean_ctor_set(v_reuseFailAlloc_1611_, 7, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1611_, 8, v_infoState_1600_);
lean_ctor_set(v_reuseFailAlloc_1611_, 9, v_snapshotTasks_1601_);
v___x_1608_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_st_ref_put(v___y_1585_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1605_);
return v___x_1610_;
}
}
}
v___jp_1613_:
{
lean_object* v_fileName_1622_; lean_object* v_fileMap_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1639_; 
v_fileName_1622_ = lean_ctor_get(v___y_1620_, 0);
v_fileMap_1623_ = lean_ctor_get(v___y_1620_, 1);
v___x_1624_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1568_);
v___x_1625_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v___x_1624_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1639_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1639_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_inc_ref_n(v_fileMap_1623_, 2);
v___x_1630_ = l_Lean_FileMap_toPosition(v_fileMap_1623_, v___y_1619_);
lean_dec(v___y_1619_);
v___x_1631_ = l_Lean_FileMap_toPosition(v_fileMap_1623_, v___y_1621_);
lean_dec(v___y_1621_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
v___x_1633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
if (v___y_1616_ == 0)
{
lean_del_object(v___x_1628_);
lean_dec_ref(v___y_1614_);
v___y_1577_ = v___x_1632_;
v___y_1578_ = v___y_1617_;
v___y_1579_ = v___x_1630_;
v___y_1580_ = v___y_1618_;
v___y_1581_ = v_a_1626_;
v___y_1582_ = v___x_1633_;
v___y_1583_ = v_fileName_1622_;
v_toCold_1584_ = v___y_1615_;
v___y_1585_ = v___y_1574_;
goto v___jp_1576_;
}
else
{
uint8_t v___x_1634_; 
lean_inc(v_a_1626_);
v___x_1634_ = l_Lean_MessageData_hasTag(v___y_1614_, v_a_1626_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_dec_ref_known(v___x_1632_, 1);
lean_dec_ref(v___x_1630_);
lean_dec(v_a_1626_);
v___x_1635_ = lean_box(0);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1635_);
v___x_1637_ = v___x_1628_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
lean_del_object(v___x_1628_);
v___y_1577_ = v___x_1632_;
v___y_1578_ = v___y_1617_;
v___y_1579_ = v___x_1630_;
v___y_1580_ = v___y_1618_;
v___y_1581_ = v_a_1626_;
v___y_1582_ = v___x_1633_;
v___y_1583_ = v_fileName_1622_;
v_toCold_1584_ = v___y_1615_;
v___y_1585_ = v___y_1574_;
goto v___jp_1576_;
}
}
}
}
v___jp_1640_:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Syntax_getTailPos_x3f(v___y_1646_, v___y_1644_);
lean_dec(v___y_1646_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_inc(v___y_1647_);
v___y_1614_ = v___y_1641_;
v___y_1615_ = v___y_1643_;
v___y_1616_ = v___y_1642_;
v___y_1617_ = v___y_1644_;
v___y_1618_ = v___y_1645_;
v___y_1619_ = v___y_1647_;
v___y_1620_ = v___y_1643_;
v___y_1621_ = v___y_1647_;
goto v___jp_1613_;
}
else
{
lean_object* v_val_1649_; 
v_val_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_val_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___y_1614_ = v___y_1641_;
v___y_1615_ = v___y_1643_;
v___y_1616_ = v___y_1642_;
v___y_1617_ = v___y_1644_;
v___y_1618_ = v___y_1645_;
v___y_1619_ = v___y_1647_;
v___y_1620_ = v___y_1643_;
v___y_1621_ = v_val_1649_;
goto v___jp_1613_;
}
}
v___jp_1650_:
{
lean_object* v_toCold_1654_; lean_object* v_ref_1655_; uint8_t v_suppressElabErrors_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___f_1659_; lean_object* v_ref_1660_; lean_object* v___x_1661_; 
v_toCold_1654_ = lean_ctor_get(v___y_1573_, 0);
v_ref_1655_ = lean_ctor_get(v___y_1573_, 2);
v_suppressElabErrors_1656_ = lean_ctor_get_uint8(v___y_1573_, sizeof(void*)*3 + 2);
v___x_1657_ = lean_box(v_suppressElabErrors_1656_);
v___x_1658_ = lean_box(v___y_1651_);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1659_, 0, v___x_1657_);
lean_closure_set(v___f_1659_, 1, v___x_1658_);
v_ref_1660_ = l_Lean_replaceRef(v_ref_1567_, v_ref_1655_);
v___x_1661_ = l_Lean_Syntax_getPos_x3f(v_ref_1660_, v___y_1652_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_unsigned_to_nat(0u);
v___y_1641_ = v___f_1659_;
v___y_1642_ = v_suppressElabErrors_1656_;
v___y_1643_ = v_toCold_1654_;
v___y_1644_ = v___y_1652_;
v___y_1645_ = v___y_1653_;
v___y_1646_ = v_ref_1660_;
v___y_1647_ = v___x_1662_;
goto v___jp_1640_;
}
else
{
lean_object* v_val_1663_; 
v_val_1663_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v___x_1661_, 1);
v___y_1641_ = v___f_1659_;
v___y_1642_ = v_suppressElabErrors_1656_;
v___y_1643_ = v_toCold_1654_;
v___y_1644_ = v___y_1652_;
v___y_1645_ = v___y_1653_;
v___y_1646_ = v_ref_1660_;
v___y_1647_ = v_val_1663_;
goto v___jp_1640_;
}
}
v___jp_1665_:
{
if (v___y_1668_ == 0)
{
v___y_1651_ = v___y_1666_;
v___y_1652_ = v___y_1667_;
v___y_1653_ = v_severity_1569_;
goto v___jp_1650_;
}
else
{
v___y_1651_ = v___y_1666_;
v___y_1652_ = v___y_1667_;
v___y_1653_ = v___x_1664_;
goto v___jp_1650_;
}
}
v___jp_1669_:
{
if (v___y_1670_ == 0)
{
uint8_t v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = 1;
v___x_1672_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1569_, v___x_1671_);
if (v___x_1672_ == 0)
{
v___y_1666_ = v___y_1670_;
v___y_1667_ = v___y_1670_;
v___y_1668_ = v___x_1672_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1673_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1573_);
v___x_1674_ = l_Lean_warningAsError;
v___x_1675_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v___x_1673_, v___x_1674_);
lean_dec_ref(v___x_1673_);
v___y_1666_ = v___y_1670_;
v___y_1667_ = v___y_1670_;
v___y_1668_ = v___x_1675_;
goto v___jp_1665_;
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v_msgData_1568_);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1680_, lean_object* v_msgData_1681_, lean_object* v_severity_1682_, lean_object* v_isSilent_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v_severity_boxed_1689_; uint8_t v_isSilent_boxed_1690_; lean_object* v_res_1691_; 
v_severity_boxed_1689_ = lean_unbox(v_severity_1682_);
v_isSilent_boxed_1690_ = lean_unbox(v_isSilent_1683_);
v_res_1691_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1680_, v_msgData_1681_, v_severity_boxed_1689_, v_isSilent_boxed_1690_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v_ref_1680_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(lean_object* v_msgData_1692_, uint8_t v_severity_1693_, uint8_t v_isSilent_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_ref_1702_; lean_object* v___x_1703_; 
v_ref_1702_ = lean_ctor_get(v___y_1699_, 2);
v___x_1703_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1702_, v_msgData_1692_, v_severity_1693_, v_isSilent_1694_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1704_, lean_object* v_severity_1705_, lean_object* v_isSilent_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v_severity_boxed_1714_; uint8_t v_isSilent_boxed_1715_; lean_object* v_res_1716_; 
v_severity_boxed_1714_ = lean_unbox(v_severity_1705_);
v_isSilent_boxed_1715_ = lean_unbox(v_isSilent_1706_);
v_res_1716_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1704_, v_severity_boxed_1714_, v_isSilent_boxed_1715_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(lean_object* v_msgData_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = 2;
v___x_1726_ = 0;
v___x_1727_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1717_, v___x_1725_, v___x_1726_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1___boxed(lean_object* v_msgData_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v_msgData_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(lean_object* v_ref_1737_, lean_object* v_msgData_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = 2;
v___x_1747_ = 0;
v___x_1748_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1737_, v_msgData_1738_, v___x_1746_, v___x_1747_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0___boxed(lean_object* v_ref_1749_, lean_object* v_msgData_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1749_, v_msgData_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v_ref_1749_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0));
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(lean_object* v_ex_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
if (lean_obj_tag(v_ex_1762_) == 0)
{
lean_object* v_ref_1770_; lean_object* v_msg_1771_; lean_object* v___x_1772_; 
v_ref_1770_ = lean_ctor_get(v_ex_1762_, 0);
lean_inc(v_ref_1770_);
v_msg_1771_ = lean_ctor_get(v_ex_1762_, 1);
lean_inc_ref(v_msg_1771_);
lean_dec_ref_known(v_ex_1762_, 2);
v___x_1772_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1770_, v_msg_1771_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v_ref_1770_);
return v___x_1772_;
}
else
{
lean_object* v_id_1773_; uint8_t v___y_1775_; uint8_t v___x_1797_; 
v_id_1773_ = lean_ctor_get(v_ex_1762_, 0);
lean_inc(v_id_1773_);
v___x_1797_ = l_Lean_Elab_isAbortExceptionId(v_id_1773_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lean_Exception_isInterrupt(v_ex_1762_);
lean_dec_ref_known(v_ex_1762_, 2);
v___y_1775_ = v___x_1798_;
goto v___jp_1774_;
}
else
{
lean_dec_ref_known(v_ex_1762_, 2);
v___y_1775_ = v___x_1797_;
goto v___jp_1774_;
}
v___jp_1774_:
{
if (v___y_1775_ == 0)
{
lean_object* v_ref_1776_; lean_object* v___x_1777_; 
v_ref_1776_ = lean_ctor_get(v___y_1767_, 2);
v___x_1777_ = l_Lean_InternalExceptionId_getName(v_id_1773_);
lean_dec(v_id_1773_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1);
v___x_1780_ = l_Lean_MessageData_ofName(v_a_1778_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v___x_1781_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1782_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1794_; 
v_a_1783_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1785_ = v___x_1777_;
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1777_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1787_ = lean_io_error_to_string(v_a_1783_);
v___x_1788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
v___x_1789_ = l_Lean_MessageData_ofFormat(v___x_1788_);
lean_inc(v_ref_1776_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_ref_1776_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1790_);
v___x_1792_ = v___x_1785_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_id_1773_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___boxed(lean_object* v_ex_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v_ex_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(lean_object* v_t_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v_infoState_1812_; uint8_t v_enabled_1813_; 
v___x_1811_ = lean_st_ref_get(v___y_1809_);
v_infoState_1812_ = lean_ctor_get(v___x_1811_, 8);
lean_inc_ref(v_infoState_1812_);
lean_dec(v___x_1811_);
v_enabled_1813_ = lean_ctor_get_uint8(v_infoState_1812_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1812_);
if (v_enabled_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec_ref(v_t_1808_);
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v_infoState_1817_; lean_object* v_env_1818_; lean_object* v_nextMacroScope_1819_; lean_object* v_ngen_1820_; lean_object* v_auxDeclNGen_1821_; lean_object* v_traceState_1822_; lean_object* v_cache_1823_; lean_object* v_recordedDeps_1824_; lean_object* v_messages_1825_; lean_object* v_snapshotTasks_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1848_; 
v___x_1816_ = lean_st_ref_take(v___y_1809_);
v_infoState_1817_ = lean_ctor_get(v___x_1816_, 8);
v_env_1818_ = lean_ctor_get(v___x_1816_, 0);
v_nextMacroScope_1819_ = lean_ctor_get(v___x_1816_, 1);
v_ngen_1820_ = lean_ctor_get(v___x_1816_, 2);
v_auxDeclNGen_1821_ = lean_ctor_get(v___x_1816_, 3);
v_traceState_1822_ = lean_ctor_get(v___x_1816_, 4);
v_cache_1823_ = lean_ctor_get(v___x_1816_, 5);
v_recordedDeps_1824_ = lean_ctor_get(v___x_1816_, 6);
v_messages_1825_ = lean_ctor_get(v___x_1816_, 7);
v_snapshotTasks_1826_ = lean_ctor_get(v___x_1816_, 9);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1828_ = v___x_1816_;
v_isShared_1829_ = v_isSharedCheck_1848_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_snapshotTasks_1826_);
lean_inc(v_infoState_1817_);
lean_inc(v_messages_1825_);
lean_inc(v_recordedDeps_1824_);
lean_inc(v_cache_1823_);
lean_inc(v_traceState_1822_);
lean_inc(v_auxDeclNGen_1821_);
lean_inc(v_ngen_1820_);
lean_inc(v_nextMacroScope_1819_);
lean_inc(v_env_1818_);
lean_dec(v___x_1816_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1848_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
uint8_t v_enabled_1830_; lean_object* v_assignment_1831_; lean_object* v_lazyAssignment_1832_; lean_object* v_trees_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1847_; 
v_enabled_1830_ = lean_ctor_get_uint8(v_infoState_1817_, sizeof(void*)*3);
v_assignment_1831_ = lean_ctor_get(v_infoState_1817_, 0);
v_lazyAssignment_1832_ = lean_ctor_get(v_infoState_1817_, 1);
v_trees_1833_ = lean_ctor_get(v_infoState_1817_, 2);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_infoState_1817_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1835_ = v_infoState_1817_;
v_isShared_1836_ = v_isSharedCheck_1847_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_trees_1833_);
lean_inc(v_lazyAssignment_1832_);
lean_inc(v_assignment_1831_);
lean_dec(v_infoState_1817_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1847_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = l_Lean_PersistentArray_push___redArg(v_trees_1833_, v_t_1808_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 2, v___x_1838_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_assignment_1831_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_lazyAssignment_1832_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v___x_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, sizeof(void*)*3, v_enabled_1830_);
v___x_1840_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 8, v___x_1840_);
v___x_1842_ = v___x_1828_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_env_1818_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_nextMacroScope_1819_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_ngen_1820_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_auxDeclNGen_1821_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_traceState_1822_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_cache_1823_);
lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_recordedDeps_1824_);
lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_messages_1825_);
lean_ctor_set(v_reuseFailAlloc_1845_, 8, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_snapshotTasks_1826_);
v___x_1842_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_st_ref_put(v___y_1809_, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1837_);
return v___x_1844_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_t_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_1849_, v___y_1850_);
lean_dec(v___y_1850_);
return v_res_1852_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_unsigned_to_nat(32u);
v___x_1854_ = lean_mk_empty_array_with_capacity(v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1856_ = ((size_t)5ULL);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_unsigned_to_nat(32u);
v___x_1859_ = lean_mk_empty_array_with_capacity(v___x_1858_);
v___x_1860_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0);
v___x_1861_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1859_);
lean_ctor_set(v___x_1861_, 2, v___x_1857_);
lean_ctor_set(v___x_1861_, 3, v___x_1857_);
lean_ctor_set_usize(v___x_1861_, 4, v___x_1856_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(lean_object* v_t_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v_infoState_1871_; uint8_t v_enabled_1872_; 
v___x_1870_ = lean_st_ref_get(v___y_1868_);
v_infoState_1871_ = lean_ctor_get(v___x_1870_, 8);
lean_inc_ref(v_infoState_1871_);
lean_dec(v___x_1870_);
v_enabled_1872_ = lean_ctor_get_uint8(v_infoState_1871_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1871_);
if (v_enabled_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec_ref(v_t_1862_);
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
v___x_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_t_1862_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v___x_1876_, v___y_1868_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___boxed(lean_object* v_t_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v_t_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(lean_object* v_info_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_info_1887_);
v___x_1896_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v___x_1895_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1___boxed(lean_object* v_info_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v_info_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1905_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13));
v___x_1945_ = l_String_toRawSubstring_x27(v___x_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9));
v___x_1969_ = l_String_toRawSubstring_x27(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(uint8_t v___x_1984_, lean_object* v_option_1985_, lean_object* v_fst_1986_, uint8_t v___x_1987_, lean_object* v_fst_1988_, lean_object* v_fst_1989_, lean_object* v_snd_1990_, lean_object* v_mkStructInst_1991_, lean_object* v_seenFields_1992_, lean_object* v_fields_1993_, lean_object* v_value_1994_, lean_object* v_____r_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___y_2004_; lean_object* v_source_x3f_2005_; lean_object* v_seenFields_2006_; lean_object* v_fields_2007_; lean_object* v___y_2008_; lean_object* v_value_2032_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8));
lean_inc(v_value_1994_);
v___x_2046_ = l_Lean_Syntax_isOfKind(v_value_1994_, v___x_2045_);
if (v___x_2046_ == 0)
{
v_value_2032_ = v_value_1994_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(1u);
v___x_2048_ = l_Lean_Syntax_getArg(v_value_1994_, v___x_2047_);
if (v___x_1984_ == 0)
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10));
lean_inc(v___x_2048_);
v___x_2079_ = l_Lean_Syntax_isOfKind(v___x_2048_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_dec(v___x_2048_);
v_value_2032_ = v_value_1994_;
goto v___jp_2031_;
}
else
{
goto v___jp_2049_;
}
}
else
{
goto v___jp_2049_;
}
v___jp_2049_:
{
lean_object* v_toCold_2050_; lean_object* v_ref_2051_; lean_object* v_quotContext_2052_; lean_object* v_currMacroScope_2053_; lean_object* v_ref_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_toCold_2050_ = lean_ctor_get(v___y_2000_, 0);
v_ref_2051_ = lean_ctor_get(v___y_2000_, 2);
v_quotContext_2052_ = lean_ctor_get(v_toCold_2050_, 8);
v_currMacroScope_2053_ = lean_ctor_get(v_toCold_2050_, 9);
v_ref_2054_ = l_Lean_replaceRef(v_value_1994_, v_ref_2051_);
lean_dec(v_value_1994_);
v___x_2055_ = l_Lean_SourceInfo_fromRef(v_ref_2054_, v___x_1984_);
lean_dec(v_ref_2054_);
v___x_2056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_2057_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14);
v___x_2058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17));
lean_inc_n(v_currMacroScope_2053_, 2);
lean_inc_n(v_quotContext_2052_, 2);
v___x_2059_ = l_Lean_addMacroScope(v_quotContext_2052_, v___x_2058_, v_currMacroScope_2053_);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20));
lean_inc_n(v___x_2055_, 7);
v___x_2061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2055_);
lean_ctor_set(v___x_2061_, 1, v___x_2057_);
lean_ctor_set(v___x_2061_, 2, v___x_2059_);
lean_ctor_set(v___x_2061_, 3, v___x_2060_);
v___x_2062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22));
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23));
v___x_2065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2055_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24);
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25));
v___x_2068_ = l_Lean_addMacroScope(v_quotContext_2052_, v___x_2067_, v_currMacroScope_2053_);
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29));
v___x_2070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2055_);
lean_ctor_set(v___x_2070_, 1, v___x_2066_);
lean_ctor_set(v___x_2070_, 2, v___x_2068_);
lean_ctor_set(v___x_2070_, 3, v___x_2069_);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30));
v___x_2072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2055_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_2074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2055_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_Syntax_node5(v___x_2055_, v___x_2063_, v___x_2065_, v___x_2070_, v___x_2072_, v___x_2048_, v___x_2074_);
v___x_2076_ = l_Lean_Syntax_node1(v___x_2055_, v___x_2062_, v___x_2075_);
v___x_2077_ = l_Lean_Syntax_node2(v___x_2055_, v___x_2056_, v___x_2061_, v___x_2076_);
v_value_2032_ = v___x_2077_;
goto v___jp_2031_;
}
}
v___jp_2003_:
{
lean_object* v_ref_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_ref_2009_ = lean_ctor_get(v___y_2008_, 2);
v___x_2010_ = l_Lean_SourceInfo_fromRef(v_ref_2009_, v___x_1984_);
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1));
v___x_2012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3));
lean_inc(v_fst_1986_);
v___x_2013_ = l_Lean_mkCIdentFrom(v_option_1985_, v_fst_1986_, v___x_1987_);
v___x_2014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2010_, 5);
v___x_2016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2010_);
lean_ctor_set(v___x_2016_, 1, v___x_2014_);
lean_ctor_set(v___x_2016_, 2, v___x_2015_);
lean_inc_ref_n(v___x_2016_, 3);
v___x_2017_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2012_, v___x_2013_, v___x_2016_);
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5));
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_2020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2010_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_Syntax_node3(v___x_2010_, v___x_2018_, v___x_2020_, v___x_2016_, v___y_2004_);
v___x_2022_ = l_Lean_Syntax_node3(v___x_2010_, v___x_2014_, v___x_2016_, v___x_2016_, v___x_2021_);
v___x_2023_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2011_, v___x_2017_, v___x_2022_);
v___x_2024_ = lean_array_push(v_fields_2007_, v___x_2023_);
v___x_2025_ = l_Lean_NameSet_insert(v_seenFields_2006_, v_fst_1986_);
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2024_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_source_x3f_2005_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2026_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
v___jp_2031_:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Lean_NameSet_contains(v_fst_1988_, v_fst_1986_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v_fields_1993_);
lean_dec(v_seenFields_1992_);
lean_dec_ref(v_mkStructInst_1991_);
v___y_2004_ = v_value_2032_;
v_source_x3f_2005_ = v_fst_1989_;
v_seenFields_2006_ = v_fst_1988_;
v_fields_2007_ = v_snd_1990_;
v___y_2008_ = v___y_2000_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2034_; 
lean_dec(v_fst_1988_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
v___x_2034_ = lean_apply_9(v_mkStructInst_1991_, v_fst_1989_, v_snd_1990_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, lean_box(0));
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_a_2035_);
v___y_2004_ = v_value_2032_;
v_source_x3f_2005_ = v___x_2036_;
v_seenFields_2006_ = v_seenFields_1992_;
v_fields_2007_ = v_fields_1993_;
v___y_2008_ = v___y_2000_;
goto v___jp_2003_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_value_2032_);
lean_dec_ref(v_fields_1993_);
lean_dec(v_seenFields_1992_);
lean_dec(v_fst_1986_);
v_a_2037_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2034_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2034_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v___x_2080_ = _args[0];
lean_object* v_option_2081_ = _args[1];
lean_object* v_fst_2082_ = _args[2];
lean_object* v___x_2083_ = _args[3];
lean_object* v_fst_2084_ = _args[4];
lean_object* v_fst_2085_ = _args[5];
lean_object* v_snd_2086_ = _args[6];
lean_object* v_mkStructInst_2087_ = _args[7];
lean_object* v_seenFields_2088_ = _args[8];
lean_object* v_fields_2089_ = _args[9];
lean_object* v_value_2090_ = _args[10];
lean_object* v_____r_2091_ = _args[11];
lean_object* v___y_2092_ = _args[12];
lean_object* v___y_2093_ = _args[13];
lean_object* v___y_2094_ = _args[14];
lean_object* v___y_2095_ = _args[15];
lean_object* v___y_2096_ = _args[16];
lean_object* v___y_2097_ = _args[17];
lean_object* v___y_2098_ = _args[18];
_start:
{
uint8_t v___x_50200__boxed_2099_; uint8_t v___x_50202__boxed_2100_; lean_object* v_res_2101_; 
v___x_50200__boxed_2099_ = lean_unbox(v___x_2080_);
v___x_50202__boxed_2100_ = lean_unbox(v___x_2083_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_50200__boxed_2099_, v_option_2081_, v_fst_2082_, v___x_50202__boxed_2100_, v_fst_2084_, v_fst_2085_, v_snd_2086_, v_mkStructInst_2087_, v_seenFields_2088_, v_fields_2089_, v_value_2090_, v_____r_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v_option_2081_);
return v_res_2101_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2106_ = lean_box(1);
v___x_2107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1);
v___x_2109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2107_);
lean_ctor_set(v___x_2109_, 2, v___x_2106_);
return v___x_2109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_box(0);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3));
v___x_2114_ = l_Lean_Expr_const___override(v___x_2113_, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(lean_object* v_structName_2121_, uint8_t v_recover_2122_, lean_object* v_as_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_fst_2135_; lean_object* v_fst_2136_; lean_object* v_snd_2137_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec(v_structName_2121_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_b_2126_);
return v___x_2145_;
}
else
{
lean_object* v_snd_2146_; lean_object* v_fst_2147_; lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2255_; 
v_snd_2146_ = lean_ctor_get(v_b_2126_, 1);
lean_inc(v_snd_2146_);
v_fst_2147_ = lean_ctor_get(v_b_2126_, 0);
lean_inc(v_fst_2147_);
lean_dec_ref(v_b_2126_);
v_fst_2148_ = lean_ctor_get(v_snd_2146_, 0);
v_snd_2149_ = lean_ctor_get(v_snd_2146_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_snd_2146_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2151_ = v_snd_2146_;
v_isShared_2152_ = v_isSharedCheck_2255_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_inc(v_fst_2148_);
lean_dec(v_snd_2146_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2255_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___y_2154_; uint8_t v___y_2155_; lean_object* v_a_2168_; lean_object* v___y_2172_; lean_object* v_a_2180_; lean_object* v_ref_2181_; lean_object* v_option_2182_; lean_object* v_value_2183_; uint8_t v_bool_2184_; lean_object* v_mkStructInst_2185_; lean_object* v_seenFields_2186_; lean_object* v_fields_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_a_2180_ = lean_array_uget_borrowed(v_as_2123_, v_i_2125_);
v_ref_2181_ = lean_ctor_get(v_a_2180_, 0);
v_option_2182_ = lean_ctor_get(v_a_2180_, 1);
v_value_2183_ = lean_ctor_get(v_a_2180_, 2);
v_bool_2184_ = lean_ctor_get_uint8(v_a_2180_, sizeof(void*)*3);
lean_inc(v_structName_2121_);
v_mkStructInst_2185_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed), 10, 1);
lean_closure_set(v_mkStructInst_2185_, 0, v_structName_2121_);
v_seenFields_2186_ = l_Lean_NameSet_empty;
v_fields_2187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v___x_2188_ = l_Lean_TSyntax_getId(v_option_2182_);
v___x_2189_ = l_Lean_Name_eraseMacroScopes(v___x_2188_);
lean_dec(v___x_2188_);
v___x_2190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7));
v___x_2191_ = lean_name_eq(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2192_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
lean_inc(v___x_2189_);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2189_);
lean_inc(v_structName_2121_);
lean_inc(v_option_2182_);
v___x_2194_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2194_, 0, v_option_2182_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_ctor_set(v___x_2194_, 2, v___x_2192_);
lean_ctor_set(v___x_2194_, 3, v_structName_2121_);
v___x_2195_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v___x_2194_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_toCold_2196_; lean_object* v_currRecDepth_2197_; lean_object* v_ref_2198_; uint16_t v_optionFlags_2199_; uint8_t v_suppressElabErrors_2200_; uint8_t v_isRecordingDeps_2201_; lean_object* v_ref_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref_known(v___x_2195_, 1);
v_toCold_2196_ = lean_ctor_get(v___y_2131_, 0);
v_currRecDepth_2197_ = lean_ctor_get(v___y_2131_, 1);
v_ref_2198_ = lean_ctor_get(v___y_2131_, 2);
v_optionFlags_2199_ = lean_ctor_get_uint16(v___y_2131_, sizeof(void*)*3);
v_suppressElabErrors_2200_ = lean_ctor_get_uint8(v___y_2131_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2201_ = lean_ctor_get_uint8(v___y_2131_, sizeof(void*)*3 + 3);
v_ref_2202_ = l_Lean_replaceRef(v_option_2182_, v_ref_2198_);
lean_inc(v_currRecDepth_2197_);
lean_inc_ref(v_toCold_2196_);
v___x_2203_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2203_, 0, v_toCold_2196_);
lean_ctor_set(v___x_2203_, 1, v_currRecDepth_2197_);
lean_ctor_set(v___x_2203_, 2, v_ref_2202_);
lean_ctor_set_uint16(v___x_2203_, sizeof(void*)*3, v_optionFlags_2199_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*3 + 2, v_suppressElabErrors_2200_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*3 + 3, v_isRecordingDeps_2201_);
lean_inc(v___x_2189_);
lean_inc(v_structName_2121_);
v___x_2204_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_2121_, v___x_2189_, v___y_2129_, v___y_2130_, v___x_2203_, v___y_2132_);
lean_dec_ref_known(v___x_2203_, 3);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
if (v_bool_2184_ == 0)
{
lean_object* v_fst_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v___x_2189_);
lean_del_object(v___x_2151_);
v_fst_2206_ = lean_ctor_get(v_a_2205_, 0);
lean_inc(v_fst_2206_);
lean_dec(v_a_2205_);
v___x_2207_ = lean_box(0);
lean_inc(v_value_2183_);
lean_inc(v_snd_2149_);
lean_inc(v_fst_2147_);
lean_inc(v_fst_2148_);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2191_, v_option_2182_, v_fst_2206_, v___x_2144_, v_fst_2148_, v_fst_2147_, v_snd_2149_, v_mkStructInst_2185_, v_seenFields_2186_, v_fields_2187_, v_value_2183_, v___x_2207_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v___y_2172_ = v___x_2208_;
goto v___jp_2171_;
}
else
{
lean_object* v_fst_2209_; lean_object* v_snd_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2236_; 
v_fst_2209_ = lean_ctor_get(v_a_2205_, 0);
v_snd_2210_ = lean_ctor_get(v_a_2205_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_a_2205_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2212_ = v_a_2205_;
v_isShared_2213_ = v_isSharedCheck_2236_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_snd_2210_);
lean_inc(v_fst_2209_);
lean_dec(v_a_2205_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2236_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_snd_2210_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = l_Lean_ConstantInfo_type(v_a_2215_);
lean_dec(v_a_2215_);
v___x_2217_ = l_Lean_Expr_bindingBody_x21(v___x_2216_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4);
v___x_2219_ = lean_expr_eqv(v___x_2217_, v___x_2218_);
lean_dec_ref(v___x_2217_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2220_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6);
v___x_2221_ = l_Lean_MessageData_ofName(v___x_2189_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 7);
lean_ctor_set(v___x_2212_, 1, v___x_2221_);
lean_ctor_set(v___x_2212_, 0, v___x_2220_);
v___x_2223_ = v___x_2212_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8);
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 7);
lean_ctor_set(v___x_2151_, 1, v___x_2224_);
lean_ctor_set(v___x_2151_, 0, v___x_2223_);
v___x_2226_ = v___x_2151_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_2181_, v___x_2226_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
lean_inc(v_value_2183_);
lean_inc(v_snd_2149_);
lean_inc(v_fst_2147_);
lean_inc(v_fst_2148_);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2191_, v_option_2182_, v_fst_2209_, v___x_2144_, v_fst_2148_, v_fst_2147_, v_snd_2149_, v_mkStructInst_2185_, v_seenFields_2186_, v_fields_2187_, v_value_2183_, v_a_2228_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v___y_2172_ = v___x_2229_;
goto v___jp_2171_;
}
else
{
lean_object* v_a_2230_; 
lean_dec(v_fst_2209_);
lean_dec_ref(v_mkStructInst_2185_);
v_a_2230_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2227_, 1);
v_a_2168_ = v_a_2230_;
goto v___jp_2167_;
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_del_object(v___x_2212_);
lean_dec(v___x_2189_);
lean_del_object(v___x_2151_);
v___x_2233_ = lean_box(0);
lean_inc(v_value_2183_);
lean_inc(v_snd_2149_);
lean_inc(v_fst_2147_);
lean_inc(v_fst_2148_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2191_, v_option_2182_, v_fst_2209_, v___x_2144_, v_fst_2148_, v_fst_2147_, v_snd_2149_, v_mkStructInst_2185_, v_seenFields_2186_, v_fields_2187_, v_value_2183_, v___x_2233_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v___y_2172_ = v___x_2234_;
goto v___jp_2171_;
}
}
else
{
lean_object* v_a_2235_; 
lean_del_object(v___x_2212_);
lean_dec(v_fst_2209_);
lean_dec(v___x_2189_);
lean_dec_ref(v_mkStructInst_2185_);
lean_del_object(v___x_2151_);
v_a_2235_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2214_, 1);
v_a_2168_ = v_a_2235_;
goto v___jp_2167_;
}
}
}
}
else
{
lean_object* v_a_2237_; 
lean_dec(v___x_2189_);
lean_dec_ref(v_mkStructInst_2185_);
lean_del_object(v___x_2151_);
v_a_2237_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2204_, 1);
v_a_2168_ = v_a_2237_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_a_2238_; 
lean_dec(v___x_2189_);
lean_dec_ref(v_mkStructInst_2185_);
lean_del_object(v___x_2151_);
v_a_2238_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2195_, 1);
v_a_2168_ = v_a_2238_;
goto v___jp_2167_;
}
}
else
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
lean_dec(v___x_2189_);
lean_dec_ref(v_mkStructInst_2185_);
lean_del_object(v___x_2151_);
v___x_2239_ = lean_array_get_size(v_snd_2149_);
v___x_2240_ = lean_nat_dec_eq(v___x_2239_, v___x_2143_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_inc(v_fst_2147_);
lean_inc(v_structName_2121_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_2121_, v_fst_2147_, v_snd_2149_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2251_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 1);
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_box(0);
lean_inc(v_structName_2121_);
lean_inc(v_a_2180_);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2180_, v_structName_2121_, v___x_2248_, v___x_2247_, v_seenFields_2186_, v_fields_2187_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v___y_2172_ = v___x_2249_;
goto v___jp_2171_;
}
}
}
else
{
lean_object* v_a_2252_; 
v_a_2252_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2241_, 1);
v_a_2168_ = v_a_2252_;
goto v___jp_2167_;
}
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_box(0);
lean_inc(v_snd_2149_);
lean_inc(v_fst_2148_);
lean_inc(v_fst_2147_);
lean_inc(v_structName_2121_);
lean_inc(v_a_2180_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2180_, v_structName_2121_, v___x_2253_, v_fst_2147_, v_fst_2148_, v_snd_2149_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v___y_2172_ = v___x_2254_;
goto v___jp_2171_;
}
}
v___jp_2153_:
{
if (v___y_2155_ == 0)
{
if (v_recover_2122_ == 0)
{
lean_object* v___x_2156_; 
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2147_);
lean_dec(v_structName_2121_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2154_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v___y_2154_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_dec_ref_known(v___x_2157_, 1);
v_fst_2135_ = v_fst_2147_;
v_fst_2136_ = v_fst_2148_;
v_snd_2137_ = v_snd_2149_;
goto v___jp_2134_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2147_);
lean_dec(v_structName_2121_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
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
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v___x_2166_; 
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2147_);
lean_dec(v_structName_2121_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___y_2154_);
return v___x_2166_;
}
}
v___jp_2167_:
{
uint8_t v___x_2169_; 
v___x_2169_ = l_Lean_Exception_isInterrupt(v_a_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; 
lean_inc_ref(v_a_2168_);
v___x_2170_ = l_Lean_Exception_isRuntime(v_a_2168_);
v___y_2154_ = v_a_2168_;
v___y_2155_ = v___x_2170_;
goto v___jp_2153_;
}
else
{
v___y_2154_ = v_a_2168_;
v___y_2155_ = v___x_2169_;
goto v___jp_2153_;
}
}
v___jp_2171_:
{
if (lean_obj_tag(v___y_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v_snd_2174_; lean_object* v_snd_2175_; lean_object* v_fst_2176_; lean_object* v_fst_2177_; lean_object* v_snd_2178_; 
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2147_);
v_a_2173_ = lean_ctor_get(v___y_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___y_2172_, 1);
v_snd_2174_ = lean_ctor_get(v_a_2173_, 1);
lean_inc(v_snd_2174_);
lean_dec(v_a_2173_);
v_snd_2175_ = lean_ctor_get(v_snd_2174_, 1);
lean_inc(v_snd_2175_);
v_fst_2176_ = lean_ctor_get(v_snd_2174_, 0);
lean_inc(v_fst_2176_);
lean_dec(v_snd_2174_);
v_fst_2177_ = lean_ctor_get(v_snd_2175_, 0);
lean_inc(v_fst_2177_);
v_snd_2178_ = lean_ctor_get(v_snd_2175_, 1);
lean_inc(v_snd_2178_);
lean_dec(v_snd_2175_);
v_fst_2135_ = v_fst_2176_;
v_fst_2136_ = v_fst_2177_;
v_snd_2137_ = v_snd_2178_;
goto v___jp_2134_;
}
else
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___y_2172_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___y_2172_, 1);
v_a_2168_ = v_a_2179_;
goto v___jp_2167_;
}
}
}
}
v___jp_2134_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; size_t v___x_2140_; size_t v___x_2141_; 
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_fst_2136_);
lean_ctor_set(v___x_2138_, 1, v_snd_2137_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_fst_2135_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_add(v_i_2125_, v___x_2140_);
v_i_2125_ = v___x_2141_;
v_b_2126_ = v___x_2139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___boxed(lean_object* v_structName_2256_, lean_object* v_recover_2257_, lean_object* v_as_2258_, lean_object* v_sz_2259_, lean_object* v_i_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_recover_boxed_2269_; size_t v_sz_boxed_2270_; size_t v_i_boxed_2271_; lean_object* v_res_2272_; 
v_recover_boxed_2269_ = lean_unbox(v_recover_2257_);
v_sz_boxed_2270_ = lean_unbox_usize(v_sz_2259_);
lean_dec(v_sz_2259_);
v_i_boxed_2271_ = lean_unbox_usize(v_i_2260_);
lean_dec(v_i_2260_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2256_, v_recover_boxed_2269_, v_as_2258_, v_sz_boxed_2270_, v_i_boxed_2271_, v_b_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_as_2258_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0(lean_object* v_structName_2273_, uint8_t v_recover_2274_, lean_object* v_items_2275_, size_t v_sz_2276_, size_t v___x_2277_, lean_object* v___x_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_a_2287_; lean_object* v___x_2300_; 
lean_inc(v_structName_2273_);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2273_, v_recover_2274_, v_items_2275_, v_sz_2276_, v___x_2277_, v___x_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v_snd_2302_; lean_object* v_fst_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2380_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v_snd_2302_ = lean_ctor_get(v_a_2301_, 1);
v_fst_2303_ = lean_ctor_get(v_a_2301_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_a_2301_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2305_ = v_a_2301_;
v_isShared_2306_ = v_isSharedCheck_2380_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_snd_2302_);
lean_inc(v_fst_2303_);
lean_dec(v_a_2301_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2380_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
if (lean_obj_tag(v_fst_2303_) == 0)
{
lean_object* v_snd_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2339_; 
v_snd_2307_ = lean_ctor_get(v_snd_2302_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_snd_2302_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v_snd_2302_, 0);
lean_dec(v_unused_2340_);
v___x_2309_ = v_snd_2302_;
v_isShared_2310_ = v_isSharedCheck_2339_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snd_2307_);
lean_dec(v_snd_2302_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2339_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_ref_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v_ref_2311_ = lean_ctor_get(v___y_2283_, 2);
v___x_2312_ = 0;
v___x_2313_ = l_Lean_SourceInfo_fromRef(v_ref_2311_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2313_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 2);
lean_ctor_set(v___x_2309_, 1, v___x_2315_);
lean_ctor_set(v___x_2309_, 0, v___x_2313_);
v___x_2317_ = v___x_2309_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2313_, 5);
v___x_2320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2313_);
lean_ctor_set(v___x_2320_, 1, v___x_2318_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
v___x_2321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2323_ = l_Lean_Syntax_SepArray_ofElems(v___x_2322_, v_snd_2307_);
lean_dec(v_snd_2307_);
v___x_2324_ = l_Array_append___redArg(v___x_2319_, v___x_2323_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2313_);
lean_ctor_set(v___x_2325_, 1, v___x_2318_);
lean_ctor_set(v___x_2325_, 2, v___x_2324_);
v___x_2326_ = l_Lean_Syntax_node1(v___x_2313_, v___x_2321_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_2320_);
v___x_2328_ = l_Lean_Syntax_node1(v___x_2313_, v___x_2327_, v___x_2320_);
v___x_2329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
if (v_isShared_2306_ == 0)
{
lean_ctor_set_tag(v___x_2305_, 2);
lean_ctor_set(v___x_2305_, 1, v___x_2329_);
lean_ctor_set(v___x_2305_, 0, v___x_2313_);
v___x_2331_ = v___x_2305_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_inc(v_structName_2273_);
v___x_2332_ = l_Lean_mkCIdent(v_structName_2273_);
lean_inc_n(v___x_2313_, 2);
v___x_2333_ = l_Lean_Syntax_node2(v___x_2313_, v___x_2318_, v___x_2331_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2313_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_Syntax_node6(v___x_2313_, v___x_2314_, v___x_2317_, v___x_2320_, v___x_2326_, v___x_2328_, v___x_2333_, v___x_2335_);
v_a_2287_ = v___x_2336_;
goto v___jp_2286_;
}
}
}
}
else
{
lean_object* v_snd_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2378_; 
v_snd_2341_ = lean_ctor_get(v_snd_2302_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_snd_2302_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_snd_2302_, 0);
lean_dec(v_unused_2379_);
v___x_2343_ = v_snd_2302_;
v_isShared_2344_ = v_isSharedCheck_2378_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_snd_2341_);
lean_dec(v_snd_2302_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2378_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_val_2345_; lean_object* v_ref_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v_val_2345_ = lean_ctor_get(v_fst_2303_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v_fst_2303_, 1);
v_ref_2346_ = lean_ctor_get(v___y_2283_, 2);
v___x_2347_ = 0;
v___x_2348_ = l_Lean_SourceInfo_fromRef(v_ref_2346_, v___x_2347_);
v___x_2349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2348_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 2);
lean_ctor_set(v___x_2343_, 1, v___x_2350_);
lean_ctor_set(v___x_2343_, 0, v___x_2348_);
v___x_2352_ = v___x_2343_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
lean_inc_n(v___x_2348_, 2);
v___x_2354_ = l_Lean_Syntax_node1(v___x_2348_, v___x_2353_, v_val_2345_);
v___x_2355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
if (v_isShared_2306_ == 0)
{
lean_ctor_set_tag(v___x_2305_, 2);
lean_ctor_set(v___x_2305_, 1, v___x_2355_);
lean_ctor_set(v___x_2305_, 0, v___x_2348_);
v___x_2357_ = v___x_2305_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_inc_n(v___x_2348_, 8);
v___x_2358_ = l_Lean_Syntax_node2(v___x_2348_, v___x_2353_, v___x_2354_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2360_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_2361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2362_ = l_Lean_Syntax_SepArray_ofElems(v___x_2361_, v_snd_2341_);
lean_dec(v_snd_2341_);
v___x_2363_ = l_Array_append___redArg(v___x_2360_, v___x_2362_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2348_);
lean_ctor_set(v___x_2364_, 1, v___x_2353_);
lean_ctor_set(v___x_2364_, 2, v___x_2363_);
v___x_2365_ = l_Lean_Syntax_node1(v___x_2348_, v___x_2359_, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_2367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2348_);
lean_ctor_set(v___x_2367_, 1, v___x_2353_);
lean_ctor_set(v___x_2367_, 2, v___x_2360_);
v___x_2368_ = l_Lean_Syntax_node1(v___x_2348_, v___x_2366_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_2370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2348_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
lean_inc(v_structName_2273_);
v___x_2371_ = l_Lean_mkCIdent(v_structName_2273_);
v___x_2372_ = l_Lean_Syntax_node2(v___x_2348_, v___x_2353_, v___x_2370_, v___x_2371_);
v___x_2373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2348_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node6(v___x_2348_, v___x_2349_, v___x_2352_, v___x_2358_, v___x_2365_, v___x_2368_, v___x_2372_, v___x_2374_);
v_a_2287_ = v___x_2375_;
goto v___jp_2286_;
}
}
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_structName_2273_);
v_a_2381_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2300_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2300_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = l_Lean_mkConst(v_structName_2273_, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = 1;
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_box(v___x_2291_);
v___x_2294_ = lean_box(v___x_2291_);
v___x_2295_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2295_, 0, v_a_2287_);
lean_closure_set(v___x_2295_, 1, v___x_2290_);
lean_closure_set(v___x_2295_, 2, v___x_2293_);
lean_closure_set(v___x_2295_, 3, v___x_2294_);
lean_closure_set(v___x_2295_, 4, v___x_2292_);
v___x_2296_ = 1;
v___x_2297_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2295_, v___x_2296_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_a_2298_, v___y_2282_);
return v___x_2299_;
}
else
{
return v___x_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0___boxed(lean_object* v_structName_2389_, lean_object* v_recover_2390_, lean_object* v_items_2391_, lean_object* v_sz_2392_, lean_object* v___x_2393_, lean_object* v___x_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v_recover_boxed_2402_; size_t v_sz_boxed_2403_; size_t v___x_50785__boxed_2404_; lean_object* v_res_2405_; 
v_recover_boxed_2402_ = lean_unbox(v_recover_2390_);
v_sz_boxed_2403_ = lean_unbox_usize(v_sz_2392_);
lean_dec(v_sz_2392_);
v___x_50785__boxed_2404_ = lean_unbox_usize(v___x_2393_);
lean_dec(v___x_2393_);
v_res_2405_ = l_Lean_Elab_Tactic_elabConfig___lam__0(v_structName_2389_, v_recover_boxed_2402_, v_items_2391_, v_sz_boxed_2403_, v___x_50785__boxed_2404_, v___x_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec_ref(v_items_2391_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v_env_2411_; lean_object* v___x_2412_; lean_object* v_toCold_2413_; lean_object* v_mctx_2414_; lean_object* v_currNamespace_2415_; lean_object* v_openDecls_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_ngen_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2410_ = lean_st_ref_get(v___y_2408_);
v_env_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc_ref(v_env_2411_);
lean_dec(v___x_2410_);
v___x_2412_ = lean_st_ref_get(v___y_2406_);
v_toCold_2413_ = lean_ctor_get(v___y_2407_, 0);
v_mctx_2414_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_mctx_2414_);
lean_dec(v___x_2412_);
v_currNamespace_2415_ = lean_ctor_get(v_toCold_2413_, 4);
v_openDecls_2416_ = lean_ctor_get(v_toCold_2413_, 5);
v___x_2417_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2407_);
v___x_2418_ = lean_st_ref_get(v___y_2408_);
v_ngen_2419_ = lean_ctor_get(v___x_2418_, 2);
lean_inc_ref(v_ngen_2419_);
lean_dec(v___x_2418_);
v___x_2420_ = lean_box(0);
v___x_2421_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_2416_);
lean_inc(v_currNamespace_2415_);
v___x_2422_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2422_, 0, v_env_2411_);
lean_ctor_set(v___x_2422_, 1, v___x_2420_);
lean_ctor_set(v___x_2422_, 2, v___x_2421_);
lean_ctor_set(v___x_2422_, 3, v_mctx_2414_);
lean_ctor_set(v___x_2422_, 4, v___x_2417_);
lean_ctor_set(v___x_2422_, 5, v_currNamespace_2415_);
lean_ctor_set(v___x_2422_, 6, v_openDecls_2416_);
lean_ctor_set(v___x_2422_, 7, v_ngen_2419_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; lean_object* v_toCold_2437_; lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2462_; 
v___x_2436_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2432_, v___y_2433_, v___y_2434_);
v_toCold_2437_ = lean_ctor_get(v___y_2433_, 0);
v_a_2438_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2462_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2462_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_fileMap_2442_; lean_object* v_env_2443_; lean_object* v_mctx_2444_; lean_object* v_options_2445_; lean_object* v_currNamespace_2446_; lean_object* v_openDecls_2447_; lean_object* v_ngen_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2459_; 
v_fileMap_2442_ = lean_ctor_get(v_toCold_2437_, 1);
v_env_2443_ = lean_ctor_get(v_a_2438_, 0);
v_mctx_2444_ = lean_ctor_get(v_a_2438_, 3);
v_options_2445_ = lean_ctor_get(v_a_2438_, 4);
v_currNamespace_2446_ = lean_ctor_get(v_a_2438_, 5);
v_openDecls_2447_ = lean_ctor_get(v_a_2438_, 6);
v_ngen_2448_ = lean_ctor_get(v_a_2438_, 7);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; lean_object* v_unused_2461_; 
v_unused_2460_ = lean_ctor_get(v_a_2438_, 2);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_a_2438_, 1);
lean_dec(v_unused_2461_);
v___x_2450_ = v_a_2438_;
v_isShared_2451_ = v_isSharedCheck_2459_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_ngen_2448_);
lean_inc(v_openDecls_2447_);
lean_inc(v_currNamespace_2446_);
lean_inc(v_options_2445_);
lean_inc(v_mctx_2444_);
lean_inc(v_env_2443_);
lean_dec(v_a_2438_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2459_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = lean_box(0);
lean_inc_ref(v_fileMap_2442_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 2, v_fileMap_2442_);
lean_ctor_set(v___x_2450_, 1, v___x_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_env_2443_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_fileMap_2442_);
lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_mctx_2444_);
lean_ctor_set(v_reuseFailAlloc_2458_, 4, v_options_2445_);
lean_ctor_set(v_reuseFailAlloc_2458_, 5, v_currNamespace_2446_);
lean_ctor_set(v_reuseFailAlloc_2458_, 6, v_openDecls_2447_);
lean_ctor_set(v_reuseFailAlloc_2458_, 7, v_ngen_2448_);
v___x_2454_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2456_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2454_);
v___x_2456_ = v___x_2440_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11___boxed(lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2488_; 
v___x_2478_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2479_);
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2484_);
v___x_2486_ = v___x_2481_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed(lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(lean_object* v___x_2497_, lean_object* v_ctx_x3f_2498_, size_t v_sz_2499_, size_t v_i_2500_, lean_object* v_bs_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_usize_dec_lt(v_i_2500_, v_sz_2499_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_dec_ref(v_ctx_x3f_2498_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_bs_2501_);
return v___x_2510_;
}
else
{
lean_object* v_assignment_2511_; lean_object* v_v_2512_; lean_object* v___x_2513_; lean_object* v_bs_x27_2514_; lean_object* v_a_2516_; lean_object* v_tree_2521_; lean_object* v___x_2522_; 
v_assignment_2511_ = lean_ctor_get(v___x_2497_, 0);
v_v_2512_ = lean_array_uget(v_bs_2501_, v_i_2500_);
v___x_2513_ = lean_unsigned_to_nat(0u);
v_bs_x27_2514_ = lean_array_uset(v_bs_2501_, v_i_2500_, v___x_2513_);
v_tree_2521_ = l_Lean_Elab_InfoTree_substitute(v_v_2512_, v_assignment_2511_);
lean_inc_ref(v_ctx_x3f_2498_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
v___x_2522_ = lean_apply_7(v_ctx_x3f_2498_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
if (lean_obj_tag(v_a_2523_) == 0)
{
v_a_2516_ = v_tree_2521_;
goto v___jp_2515_;
}
else
{
lean_object* v_val_2524_; lean_object* v___x_2525_; 
v_val_2524_ = lean_ctor_get(v_a_2523_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_a_2523_, 1);
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_val_2524_);
lean_ctor_set(v___x_2525_, 1, v_tree_2521_);
v_a_2516_ = v___x_2525_;
goto v___jp_2515_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_tree_2521_);
lean_dec_ref(v_bs_x27_2514_);
lean_dec_ref(v_ctx_x3f_2498_);
v_a_2526_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2522_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2522_);
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
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
v___jp_2515_:
{
size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2500_, v___x_2517_);
v___x_2519_ = lean_array_uset(v_bs_x27_2514_, v_i_2500_, v_a_2516_);
v_i_2500_ = v___x_2518_;
v_bs_2501_ = v___x_2519_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27___boxed(lean_object* v___x_2534_, lean_object* v_ctx_x3f_2535_, lean_object* v_sz_2536_, lean_object* v_i_2537_, lean_object* v_bs_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
size_t v_sz_boxed_2546_; size_t v_i_boxed_2547_; lean_object* v_res_2548_; 
v_sz_boxed_2546_ = lean_unbox_usize(v_sz_2536_);
lean_dec(v_sz_2536_);
v_i_boxed_2547_ = lean_unbox_usize(v_i_2537_);
lean_dec(v_i_2537_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2534_, v_ctx_x3f_2535_, v_sz_boxed_2546_, v_i_boxed_2547_, v_bs_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec_ref(v___x_2534_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(lean_object* v___x_2549_, lean_object* v_ctx_x3f_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
if (lean_obj_tag(v_x_2551_) == 0)
{
lean_object* v_cs_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2585_; 
v_cs_2559_ = lean_ctor_get(v_x_2551_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_x_2551_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2561_ = v_x_2551_;
v_isShared_2562_ = v_isSharedCheck_2585_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_cs_2559_);
lean_dec(v_x_2551_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2585_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v_sz_2563_ = lean_array_size(v_cs_2559_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2549_, v_ctx_x3f_2550_, v_sz_2563_, v___x_2564_, v_cs_2559_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2576_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v_a_2566_);
v___x_2571_ = v___x_2561_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2571_);
v___x_2573_ = v___x_2568_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_del_object(v___x_2561_);
v_a_2577_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2565_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2565_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v_vs_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2612_; 
v_vs_2586_ = lean_ctor_get(v_x_2551_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_x_2551_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2588_ = v_x_2551_;
v_isShared_2589_ = v_isSharedCheck_2612_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_vs_2586_);
lean_dec(v_x_2551_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2612_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
size_t v_sz_2590_; size_t v___x_2591_; lean_object* v___x_2592_; 
v_sz_2590_ = lean_array_size(v_vs_2586_);
v___x_2591_ = ((size_t)0ULL);
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2549_, v_ctx_x3f_2550_, v_sz_2590_, v___x_2591_, v_vs_2586_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2603_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v_a_2593_);
v___x_2598_ = v___x_2588_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2598_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_del_object(v___x_2588_);
v_a_2604_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2592_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2592_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(lean_object* v___x_2613_, lean_object* v_ctx_x3f_2614_, size_t v_sz_2615_, size_t v_i_2616_, lean_object* v_bs_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_usize_dec_lt(v_i_2616_, v_sz_2615_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v_ctx_x3f_2614_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_bs_2617_);
return v___x_2626_;
}
else
{
lean_object* v_v_2627_; lean_object* v___x_2628_; lean_object* v_bs_x27_2629_; lean_object* v___x_2630_; 
v_v_2627_ = lean_array_uget(v_bs_2617_, v_i_2616_);
v___x_2628_ = lean_unsigned_to_nat(0u);
v_bs_x27_2629_ = lean_array_uset(v_bs_2617_, v_i_2616_, v___x_2628_);
lean_inc_ref(v_ctx_x3f_2614_);
v___x_2630_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2613_, v_ctx_x3f_2614_, v_v_2627_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; size_t v___x_2632_; size_t v___x_2633_; lean_object* v___x_2634_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = ((size_t)1ULL);
v___x_2633_ = lean_usize_add(v_i_2616_, v___x_2632_);
v___x_2634_ = lean_array_uset(v_bs_x27_2629_, v_i_2616_, v_a_2631_);
v_i_2616_ = v___x_2633_;
v_bs_2617_ = v___x_2634_;
goto _start;
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v_bs_x27_2629_);
lean_dec_ref(v_ctx_x3f_2614_);
v_a_2636_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2630_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2630_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28___boxed(lean_object* v___x_2644_, lean_object* v_ctx_x3f_2645_, lean_object* v_sz_2646_, lean_object* v_i_2647_, lean_object* v_bs_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2646_);
lean_dec(v_sz_2646_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2647_);
lean_dec(v_i_2647_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2644_, v_ctx_x3f_2645_, v_sz_boxed_2656_, v_i_boxed_2657_, v_bs_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2644_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26___boxed(lean_object* v___x_2659_, lean_object* v_ctx_x3f_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2659_, v_ctx_x3f_2660_, v_x_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec_ref(v___x_2659_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(lean_object* v___x_2670_, lean_object* v_ctx_x3f_2671_, lean_object* v_t_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_root_2680_; lean_object* v_tail_2681_; lean_object* v_size_2682_; size_t v_shift_2683_; lean_object* v_tailOff_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2720_; 
v_root_2680_ = lean_ctor_get(v_t_2672_, 0);
v_tail_2681_ = lean_ctor_get(v_t_2672_, 1);
v_size_2682_ = lean_ctor_get(v_t_2672_, 2);
v_shift_2683_ = lean_ctor_get_usize(v_t_2672_, 4);
v_tailOff_2684_ = lean_ctor_get(v_t_2672_, 3);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_t_2672_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2686_ = v_t_2672_;
v_isShared_2687_ = v_isSharedCheck_2720_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_tailOff_2684_);
lean_inc(v_size_2682_);
lean_inc(v_tail_2681_);
lean_inc(v_root_2680_);
lean_dec(v_t_2672_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2720_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; 
lean_inc_ref(v_ctx_x3f_2671_);
v___x_2688_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2670_, v_ctx_x3f_2671_, v_root_2680_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; size_t v_sz_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v_sz_2690_ = lean_array_size(v_tail_2681_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2670_, v_ctx_x3f_2671_, v_sz_2690_, v___x_2691_, v_tail_2681_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2703_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2703_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2703_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v_a_2693_);
lean_ctor_set(v___x_2686_, 0, v_a_2689_);
v___x_2698_ = v___x_2686_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2689_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_a_2693_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_size_2682_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_tailOff_2684_);
lean_ctor_set_usize(v_reuseFailAlloc_2702_, 4, v_shift_2683_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2698_);
v___x_2700_ = v___x_2695_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
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
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2689_);
lean_del_object(v___x_2686_);
lean_dec(v_tailOff_2684_);
lean_dec(v_size_2682_);
v_a_2704_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2692_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2692_);
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
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_del_object(v___x_2686_);
lean_dec(v_tailOff_2684_);
lean_dec(v_size_2682_);
lean_dec_ref(v_tail_2681_);
lean_dec_ref(v_ctx_x3f_2671_);
v_a_2712_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2688_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2688_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22___boxed(lean_object* v___x_2721_, lean_object* v_ctx_x3f_2722_, lean_object* v_t_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v___x_2721_, v_ctx_x3f_2722_, v_t_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec_ref(v___x_2721_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(lean_object* v___y_2732_, lean_object* v_ctx_x3f_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v_a_2739_, lean_object* v_a_x3f_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v_infoState_2743_; lean_object* v_trees_2744_; lean_object* v___x_2745_; 
v___x_2742_ = lean_st_ref_get(v___y_2732_);
v_infoState_2743_ = lean_ctor_get(v___x_2742_, 8);
lean_inc_ref(v_infoState_2743_);
lean_dec(v___x_2742_);
v_trees_2744_ = lean_ctor_get(v_infoState_2743_, 2);
lean_inc_ref(v_trees_2744_);
v___x_2745_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v_infoState_2743_, v_ctx_x3f_2733_, v_trees_2744_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2732_);
lean_dec_ref(v_infoState_2743_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2785_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2785_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2785_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v_infoState_2751_; lean_object* v_env_2752_; lean_object* v_nextMacroScope_2753_; lean_object* v_ngen_2754_; lean_object* v_auxDeclNGen_2755_; lean_object* v_traceState_2756_; lean_object* v_cache_2757_; lean_object* v_recordedDeps_2758_; lean_object* v_messages_2759_; lean_object* v_snapshotTasks_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2784_; 
v___x_2750_ = lean_st_ref_take(v___y_2732_);
v_infoState_2751_ = lean_ctor_get(v___x_2750_, 8);
v_env_2752_ = lean_ctor_get(v___x_2750_, 0);
v_nextMacroScope_2753_ = lean_ctor_get(v___x_2750_, 1);
v_ngen_2754_ = lean_ctor_get(v___x_2750_, 2);
v_auxDeclNGen_2755_ = lean_ctor_get(v___x_2750_, 3);
v_traceState_2756_ = lean_ctor_get(v___x_2750_, 4);
v_cache_2757_ = lean_ctor_get(v___x_2750_, 5);
v_recordedDeps_2758_ = lean_ctor_get(v___x_2750_, 6);
v_messages_2759_ = lean_ctor_get(v___x_2750_, 7);
v_snapshotTasks_2760_ = lean_ctor_get(v___x_2750_, 9);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2762_ = v___x_2750_;
v_isShared_2763_ = v_isSharedCheck_2784_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_snapshotTasks_2760_);
lean_inc(v_infoState_2751_);
lean_inc(v_messages_2759_);
lean_inc(v_recordedDeps_2758_);
lean_inc(v_cache_2757_);
lean_inc(v_traceState_2756_);
lean_inc(v_auxDeclNGen_2755_);
lean_inc(v_ngen_2754_);
lean_inc(v_nextMacroScope_2753_);
lean_inc(v_env_2752_);
lean_dec(v___x_2750_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2784_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v_enabled_2764_; lean_object* v_assignment_2765_; lean_object* v_lazyAssignment_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2782_; 
v_enabled_2764_ = lean_ctor_get_uint8(v_infoState_2751_, sizeof(void*)*3);
v_assignment_2765_ = lean_ctor_get(v_infoState_2751_, 0);
v_lazyAssignment_2766_ = lean_ctor_get(v_infoState_2751_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_infoState_2751_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; 
v_unused_2783_ = lean_ctor_get(v_infoState_2751_, 2);
lean_dec(v_unused_2783_);
v___x_2768_ = v_infoState_2751_;
v_isShared_2769_ = v_isSharedCheck_2782_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_lazyAssignment_2766_);
lean_inc(v_assignment_2765_);
lean_dec(v_infoState_2751_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2782_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2770_ = lean_box(0);
v___x_2771_ = l_Lean_PersistentArray_append___redArg(v_a_2739_, v_a_2746_);
lean_dec(v_a_2746_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 2, v___x_2771_);
v___x_2773_ = v___x_2768_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_assignment_2765_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_lazyAssignment_2766_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v___x_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2781_, sizeof(void*)*3, v_enabled_2764_);
v___x_2773_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2775_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 8, v___x_2773_);
v___x_2775_ = v___x_2762_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_env_2752_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_nextMacroScope_2753_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_ngen_2754_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_auxDeclNGen_2755_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_traceState_2756_);
lean_ctor_set(v_reuseFailAlloc_2780_, 5, v_cache_2757_);
lean_ctor_set(v_reuseFailAlloc_2780_, 6, v_recordedDeps_2758_);
lean_ctor_set(v_reuseFailAlloc_2780_, 7, v_messages_2759_);
lean_ctor_set(v_reuseFailAlloc_2780_, 8, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2780_, 9, v_snapshotTasks_2760_);
v___x_2775_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = lean_st_ref_put(v___y_2732_, v___x_2775_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2770_);
v___x_2778_ = v___x_2748_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2770_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v_a_2739_);
v_a_2786_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2745_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2745_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v___y_2794_, lean_object* v_ctx_x3f_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v_a_2801_, lean_object* v_a_x3f_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2794_, v_ctx_x3f_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v_a_2801_, v_a_x3f_2802_);
lean_dec(v_a_x3f_2802_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; lean_object* v_infoState_2808_; lean_object* v_trees_2809_; lean_object* v___x_2810_; lean_object* v_infoState_2811_; lean_object* v_env_2812_; lean_object* v_nextMacroScope_2813_; lean_object* v_ngen_2814_; lean_object* v_auxDeclNGen_2815_; lean_object* v_traceState_2816_; lean_object* v_cache_2817_; lean_object* v_recordedDeps_2818_; lean_object* v_messages_2819_; lean_object* v_snapshotTasks_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2843_; 
v___x_2807_ = lean_st_ref_get(v___y_2805_);
v_infoState_2808_ = lean_ctor_get(v___x_2807_, 8);
lean_inc_ref(v_infoState_2808_);
lean_dec(v___x_2807_);
v_trees_2809_ = lean_ctor_get(v_infoState_2808_, 2);
lean_inc_ref(v_trees_2809_);
lean_dec_ref(v_infoState_2808_);
v___x_2810_ = lean_st_ref_take(v___y_2805_);
v_infoState_2811_ = lean_ctor_get(v___x_2810_, 8);
v_env_2812_ = lean_ctor_get(v___x_2810_, 0);
v_nextMacroScope_2813_ = lean_ctor_get(v___x_2810_, 1);
v_ngen_2814_ = lean_ctor_get(v___x_2810_, 2);
v_auxDeclNGen_2815_ = lean_ctor_get(v___x_2810_, 3);
v_traceState_2816_ = lean_ctor_get(v___x_2810_, 4);
v_cache_2817_ = lean_ctor_get(v___x_2810_, 5);
v_recordedDeps_2818_ = lean_ctor_get(v___x_2810_, 6);
v_messages_2819_ = lean_ctor_get(v___x_2810_, 7);
v_snapshotTasks_2820_ = lean_ctor_get(v___x_2810_, 9);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2822_ = v___x_2810_;
v_isShared_2823_ = v_isSharedCheck_2843_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_snapshotTasks_2820_);
lean_inc(v_infoState_2811_);
lean_inc(v_messages_2819_);
lean_inc(v_recordedDeps_2818_);
lean_inc(v_cache_2817_);
lean_inc(v_traceState_2816_);
lean_inc(v_auxDeclNGen_2815_);
lean_inc(v_ngen_2814_);
lean_inc(v_nextMacroScope_2813_);
lean_inc(v_env_2812_);
lean_dec(v___x_2810_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2843_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
uint8_t v_enabled_2824_; lean_object* v_assignment_2825_; lean_object* v_lazyAssignment_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2841_; 
v_enabled_2824_ = lean_ctor_get_uint8(v_infoState_2811_, sizeof(void*)*3);
v_assignment_2825_ = lean_ctor_get(v_infoState_2811_, 0);
v_lazyAssignment_2826_ = lean_ctor_get(v_infoState_2811_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_infoState_2811_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v_infoState_2811_, 2);
lean_dec(v_unused_2842_);
v___x_2828_ = v_infoState_2811_;
v_isShared_2829_ = v_isSharedCheck_2841_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_lazyAssignment_2826_);
lean_inc(v_assignment_2825_);
lean_dec(v_infoState_2811_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2841_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2830_ = lean_unsigned_to_nat(32u);
v___x_2831_ = lean_mk_empty_array_with_capacity(v___x_2830_);
lean_dec_ref(v___x_2831_);
v___x_2832_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 2, v___x_2832_);
v___x_2834_ = v___x_2828_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_assignment_2825_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_lazyAssignment_2826_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v___x_2832_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*3, v_enabled_2824_);
v___x_2834_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2836_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 8, v___x_2834_);
v___x_2836_ = v___x_2822_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_env_2812_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_nextMacroScope_2813_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_ngen_2814_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_auxDeclNGen_2815_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_traceState_2816_);
lean_ctor_set(v_reuseFailAlloc_2839_, 5, v_cache_2817_);
lean_ctor_set(v_reuseFailAlloc_2839_, 6, v_recordedDeps_2818_);
lean_ctor_set(v_reuseFailAlloc_2839_, 7, v_messages_2819_);
lean_ctor_set(v_reuseFailAlloc_2839_, 8, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2839_, 9, v_snapshotTasks_2820_);
v___x_2836_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_st_ref_put(v___y_2805_, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_trees_2809_);
return v___x_2838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg___boxed(lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2844_);
lean_dec(v___y_2844_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(lean_object* v_x_2847_, lean_object* v_ctx_x3f_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v_infoState_2857_; uint8_t v_enabled_2858_; 
v___x_2856_ = lean_st_ref_get(v___y_2854_);
v_infoState_2857_ = lean_ctor_get(v___x_2856_, 8);
lean_inc_ref(v_infoState_2857_);
lean_dec(v___x_2856_);
v_enabled_2858_ = lean_ctor_get_uint8(v_infoState_2857_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2857_);
if (v_enabled_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_dec_ref(v_ctx_x3f_2848_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
v___x_2859_ = lean_apply_7(v_x_2847_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, lean_box(0));
return v___x_2859_;
}
else
{
lean_object* v___x_2860_; lean_object* v_a_2861_; lean_object* v_r_2862_; 
v___x_2860_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2854_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
v_r_2862_ = lean_apply_7(v_x_2847_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, lean_box(0));
if (lean_obj_tag(v_r_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2887_; 
v_a_2863_ = lean_ctor_get(v_r_2862_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_r_2862_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2865_ = v_r_2862_;
v_isShared_2866_ = v_isSharedCheck_2887_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v_r_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2887_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
lean_inc(v_a_2863_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set_tag(v___x_2865_, 1);
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2854_, v_ctx_x3f_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v_a_2861_, v___x_2868_);
lean_dec_ref(v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2876_ == 0)
{
lean_object* v_unused_2877_; 
v_unused_2877_ = lean_ctor_get(v___x_2869_, 0);
lean_dec(v_unused_2877_);
v___x_2871_ = v___x_2869_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v___x_2869_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_a_2863_);
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2863_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_a_2863_);
v_a_2878_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2869_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2869_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_a_2888_ = lean_ctor_get(v_r_2862_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v_r_2862_, 1);
v___x_2889_ = lean_box(0);
v___x_2890_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2854_, v_ctx_x3f_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v_a_2861_, v___x_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2890_, 0);
lean_dec(v_unused_2898_);
v___x_2892_ = v___x_2890_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v___x_2890_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 1);
lean_ctor_set(v___x_2892_, 0, v_a_2888_);
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2888_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_a_2888_);
v_a_2899_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2890_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2890_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___boxed(lean_object* v_x_2907_, lean_object* v_ctx_x3f_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2907_, v_ctx_x3f_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(lean_object* v_x_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___f_2926_; lean_object* v___x_2927_; 
v___f_2926_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0));
v___x_2927_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2918_, v___f_2926_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___boxed(lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(lean_object* v_00_u03b1_2937_, lean_object* v_x_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_x_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(v_00_u03b1_2947_, v_x_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2956_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__1(void){
_start:
{
lean_object* v_fields_2959_; lean_object* v_seenFields_2960_; lean_object* v___x_2961_; 
v_fields_2959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v_seenFields_2960_ = l_Lean_NameSet_empty;
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_seenFields_2960_);
lean_ctor_set(v___x_2961_, 1, v_fields_2959_);
return v___x_2961_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__2(void){
_start:
{
lean_object* v___x_2962_; lean_object* v_source_x3f_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__1, &l_Lean_Elab_Tactic_elabConfig___closed__1_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__1);
v_source_x3f_2963_ = lean_box(0);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_source_x3f_2963_);
lean_ctor_set(v___x_2964_, 1, v___x_2962_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t v_recover_2967_, lean_object* v_structName_2968_, lean_object* v_items_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; size_t v_sz_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___closed__0));
v___x_2979_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__2, &l_Lean_Elab_Tactic_elabConfig___closed__2_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__2);
v_sz_2980_ = lean_array_size(v_items_2969_);
v___x_2981_ = lean_box(v_recover_2967_);
v___x_2982_ = lean_box_usize(v_sz_2980_);
v___x_2983_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___boxed__const__1));
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabConfig___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2984_, 0, v_structName_2968_);
lean_closure_set(v___f_2984_, 1, v___x_2981_);
lean_closure_set(v___f_2984_, 2, v_items_2969_);
lean_closure_set(v___f_2984_, 3, v___x_2982_);
lean_closure_set(v___f_2984_, 4, v___x_2983_);
lean_closure_set(v___f_2984_, 5, v___x_2979_);
v___x_2985_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed), 9, 2);
lean_closure_set(v___x_2985_, 0, lean_box(0));
lean_closure_set(v___x_2985_, 1, v___f_2984_);
v___x_2986_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed), 11, 4);
lean_closure_set(v___x_2986_, 0, lean_box(0));
lean_closure_set(v___x_2986_, 1, v___x_2977_);
lean_closure_set(v___x_2986_, 2, v___x_2978_);
lean_closure_set(v___x_2986_, 3, v___x_2985_);
v___x_2987_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v___x_2986_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___boxed(lean_object* v_recover_2988_, lean_object* v_structName_2989_, lean_object* v_items_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
uint8_t v_recover_boxed_2998_; lean_object* v_res_2999_; 
v_recover_boxed_2998_ = lean_unbox(v_recover_2988_);
v_res_2999_ = l_Lean_Elab_Tactic_elabConfig(v_recover_boxed_2998_, v_structName_2989_, v_items_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(lean_object* v_00_u03b1_3000_, lean_object* v_ref_3001_, lean_object* v_msg_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_3001_, v_msg_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_ref_3012_, lean_object* v_msg_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(v_00_u03b1_3011_, v_ref_3012_, v_msg_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v_ref_3012_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(lean_object* v_t_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_3022_, v___y_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___boxed(lean_object* v_t_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(v_t_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(lean_object* v_00_u03b1_3040_, lean_object* v_constName_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3050_, lean_object* v_constName_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(v_00_u03b1_3050_, v_constName_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(lean_object* v_00_u03b1_3060_, lean_object* v_msg_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_msg_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(v_00_u03b1_3070_, v_msg_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_3083_, v___y_3084_, v___y_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___boxed(lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___boxed(lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(lean_object* v_00_u03b1_3112_, lean_object* v_x_3113_, lean_object* v_ctx_x3f_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_3113_, v_ctx_x3f_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3123_, lean_object* v_x_3124_, lean_object* v_ctx_x3f_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(v_00_u03b1_3123_, v_x_3124_, v_ctx_x3f_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(lean_object* v_ref_3134_, lean_object* v_msgData_3135_, uint8_t v_severity_3136_, uint8_t v_isSilent_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_3134_, v_msgData_3135_, v_severity_3136_, v_isSilent_3137_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___boxed(lean_object* v_ref_3146_, lean_object* v_msgData_3147_, lean_object* v_severity_3148_, lean_object* v_isSilent_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v_severity_boxed_3157_; uint8_t v_isSilent_boxed_3158_; lean_object* v_res_3159_; 
v_severity_boxed_3157_ = lean_unbox(v_severity_3148_);
v_isSilent_boxed_3158_ = lean_unbox(v_isSilent_3149_);
v_res_3159_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(v_ref_3146_, v_msgData_3147_, v_severity_boxed_3157_, v_isSilent_boxed_3158_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v_ref_3146_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(lean_object* v_00_u03b1_3160_, lean_object* v_ref_3161_, lean_object* v_constName_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_3161_, v_constName_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b1_3171_, lean_object* v_ref_3172_, lean_object* v_constName_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(v_00_u03b1_3171_, v_ref_3172_, v_constName_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v_ref_3172_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(lean_object* v_msgData_3182_, lean_object* v_macroStack_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_3182_, v_macroStack_3183_, v___y_3188_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___boxed(lean_object* v_msgData_3192_, lean_object* v_macroStack_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(v_msgData_3192_, v_macroStack_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(lean_object* v_00_u03b1_3202_, lean_object* v_ref_3203_, lean_object* v_msg_3204_, lean_object* v_declHint_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_3203_, v_msg_3204_, v_declHint_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___boxed(lean_object* v_00_u03b1_3214_, lean_object* v_ref_3215_, lean_object* v_msg_3216_, lean_object* v_declHint_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(v_00_u03b1_3214_, v_ref_3215_, v_msg_3216_, v_declHint_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v_ref_3215_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(lean_object* v_msg_3226_, lean_object* v_declHint_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_3226_, v_declHint_3227_, v___y_3233_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___boxed(lean_object* v_msg_3236_, lean_object* v_declHint_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(v_msg_3236_, v_declHint_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
return v_res_3245_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11));
v___x_3279_ = l_String_toRawSubstring_x27(v___x_3278_);
return v___x_3279_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18));
v___x_3296_ = l_String_toRawSubstring_x27(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21));
v___x_3301_ = l_String_toRawSubstring_x27(v___x_3300_);
return v___x_3301_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31));
v___x_3326_ = l_String_toRawSubstring_x27(v___x_3325_);
return v___x_3326_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39));
v___x_3348_ = l_String_toRawSubstring_x27(v___x_3347_);
return v___x_3348_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48));
v___x_3371_ = l_String_toRawSubstring_x27(v___x_3370_);
return v___x_3371_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3382_ = l_String_toRawSubstring_x27(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71));
v___x_3426_ = l_String_toRawSubstring_x27(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77));
v___x_3438_ = l_String_toRawSubstring_x27(v___x_3437_);
return v___x_3438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83));
v___x_3453_ = l_String_toRawSubstring_x27(v___x_3452_);
return v___x_3453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89));
v___x_3469_ = l_String_toRawSubstring_x27(v___x_3468_);
return v___x_3469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114));
v___x_3537_ = l_String_toRawSubstring_x27(v___x_3536_);
return v___x_3537_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117));
v___x_3542_ = l_String_toRawSubstring_x27(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122));
v___x_3552_ = l_String_toRawSubstring_x27(v___x_3551_);
return v___x_3552_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128));
v___x_3566_ = l_String_toRawSubstring_x27(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131));
v___x_3571_ = l_String_toRawSubstring_x27(v___x_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139));
v___x_3593_ = l_String_toRawSubstring_x27(v___x_3592_);
return v___x_3593_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150));
v___x_3622_ = l_String_toRawSubstring_x27(v___x_3621_);
return v___x_3622_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168));
v___x_3663_ = l_String_toRawSubstring_x27(v___x_3662_);
return v___x_3663_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175));
v___x_3679_ = l_String_toRawSubstring_x27(v___x_3678_);
return v___x_3679_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190));
v___x_3702_ = l_String_toRawSubstring_x27(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198));
v___x_3721_ = l_String_toRawSubstring_x27(v___x_3720_);
return v___x_3721_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17));
v___x_3725_ = l_String_toRawSubstring_x27(v___x_3724_);
return v___x_3725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210(void){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209));
v___x_3748_ = l_String_toRawSubstring_x27(v___x_3747_);
return v___x_3748_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212));
v___x_3753_ = l_String_toRawSubstring_x27(v___x_3752_);
return v___x_3753_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220));
v___x_3774_ = l_String_toRawSubstring_x27(v___x_3773_);
return v___x_3774_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224));
v___x_3781_ = l_String_toRawSubstring_x27(v___x_3780_);
return v___x_3781_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232));
v___x_3796_ = l_String_toRawSubstring_x27(v___x_3795_);
return v___x_3796_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238));
v___x_3808_ = l_String_toRawSubstring_x27(v___x_3807_);
return v___x_3808_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243(void){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242));
v___x_3814_ = l_String_toRawSubstring_x27(v___x_3813_);
return v___x_3814_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246));
v___x_3820_ = l_String_toRawSubstring_x27(v___x_3819_);
return v___x_3820_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253));
v___x_3835_ = l_String_toRawSubstring_x27(v___x_3834_);
return v___x_3835_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15));
v___x_3841_ = l_String_toRawSubstring_x27(v___x_3840_);
return v___x_3841_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261));
v___x_3852_ = l_String_toRawSubstring_x27(v___x_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(lean_object* v_doc_x3f_3867_, lean_object* v_elabName_3868_, lean_object* v_type_3869_, lean_object* v_monadName_3870_, lean_object* v_adapt_3871_, lean_object* v_recover_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_quotContext_3875_; lean_object* v_currMacroScope_3876_; lean_object* v_ref_3877_; lean_object* v_ref_3878_; uint8_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___y_4015_; 
v_quotContext_3875_ = lean_ctor_get(v_a_3873_, 1);
v_currMacroScope_3876_ = lean_ctor_get(v_a_3873_, 2);
v_ref_3877_ = lean_ctor_get(v_a_3873_, 5);
v_ref_3878_ = l_Lean_replaceRef(v_type_3869_, v_ref_3877_);
v___x_3879_ = 0;
v___x_3880_ = l_Lean_SourceInfo_fromRef(v_ref_3878_, v___x_3879_);
lean_dec(v_ref_3878_);
v___x_3881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_3882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_3880_, 7);
v___x_3883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3880_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_3885_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_3886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3880_);
lean_ctor_set(v___x_3886_, 1, v___x_3884_);
lean_ctor_set(v___x_3886_, 2, v___x_3885_);
v___x_3887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
lean_inc_ref_n(v___x_3886_, 2);
v___x_3888_ = l_Lean_Syntax_node1(v___x_3880_, v___x_3887_, v___x_3886_);
v___x_3889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_3890_ = l_Lean_Syntax_node1(v___x_3880_, v___x_3889_, v___x_3886_);
v___x_3891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_3892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3880_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
lean_inc_n(v_type_3869_, 3);
v___x_3893_ = l_Lean_Syntax_node2(v___x_3880_, v___x_3884_, v___x_3892_, v_type_3869_);
v___x_3894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_3895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3880_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = l_Lean_Syntax_node6(v___x_3880_, v___x_3881_, v___x_3883_, v___x_3886_, v___x_3888_, v___x_3890_, v___x_3893_, v___x_3895_);
v___x_3897_ = l_Lean_SourceInfo_fromRef(v_ref_3877_, v___x_3879_);
v___x_3898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1));
v___x_3899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3));
lean_inc_n(v___x_3897_, 55);
v___x_3900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3897_);
lean_ctor_set(v___x_3900_, 1, v___x_3884_);
lean_ctor_set(v___x_3900_, 2, v___x_3885_);
v___x_3901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5));
v___x_3903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3897_);
lean_ctor_set(v___x_3903_, 1, v___x_3901_);
v___x_3904_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3902_, v___x_3903_);
v___x_3905_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3904_);
lean_inc_ref_n(v___x_3900_, 21);
v___x_3906_ = l_Lean_Syntax_node7(v___x_3897_, v___x_3899_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3905_, v___x_3900_);
v___x_3907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7));
v___x_3908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8));
v___x_3909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3897_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10));
v___x_3911_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12);
v___x_3912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13));
lean_inc_n(v_currMacroScope_3876_, 9);
lean_inc_n(v_quotContext_3875_, 9);
v___x_3913_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3912_, v_currMacroScope_3876_);
v___x_3914_ = lean_box(0);
v___x_3915_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3897_);
lean_ctor_set(v___x_3915_, 1, v___x_3911_);
lean_ctor_set(v___x_3915_, 2, v___x_3913_);
lean_ctor_set(v___x_3915_, 3, v___x_3914_);
lean_inc_ref(v___x_3915_);
v___x_3916_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3910_, v___x_3915_, v___x_3900_);
v___x_3917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15));
v___x_3918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17));
v___x_3919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
v___x_3920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3897_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19);
v___x_3922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20));
v___x_3923_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3922_, v_currMacroScope_3876_);
v___x_3924_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3897_);
lean_ctor_set(v___x_3924_, 1, v___x_3921_);
lean_ctor_set(v___x_3924_, 2, v___x_3923_);
lean_ctor_set(v___x_3924_, 3, v___x_3914_);
lean_inc_ref(v___x_3924_);
v___x_3925_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3924_);
v___x_3926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3897_);
lean_ctor_set(v___x_3926_, 1, v___x_3891_);
v___x_3927_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22);
v___x_3928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23));
v___x_3929_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3928_, v_currMacroScope_3876_);
v___x_3930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28));
v___x_3931_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3897_);
lean_ctor_set(v___x_3931_, 1, v___x_3927_);
lean_ctor_set(v___x_3931_, 2, v___x_3929_);
lean_ctor_set(v___x_3931_, 3, v___x_3930_);
lean_inc_ref_n(v___x_3926_, 2);
v___x_3932_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_3926_, v___x_3931_);
v___x_3933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_3934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3897_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
lean_inc_ref_n(v___x_3934_, 2);
lean_inc_ref_n(v___x_3920_, 2);
v___x_3935_ = l_Lean_Syntax_node5(v___x_3897_, v___x_3918_, v___x_3920_, v___x_3925_, v___x_3932_, v___x_3900_, v___x_3934_);
v___x_3936_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3935_);
v___x_3937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30));
v___x_3938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_3939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32);
v___x_3940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33));
v___x_3941_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3940_, v_currMacroScope_3876_);
v___x_3942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36));
v___x_3943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3897_);
lean_ctor_set(v___x_3943_, 1, v___x_3939_);
lean_ctor_set(v___x_3943_, 2, v___x_3941_);
lean_ctor_set(v___x_3943_, 3, v___x_3942_);
v___x_3944_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v_type_3869_);
lean_inc(v___x_3944_);
v___x_3945_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_3943_, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3937_, v___x_3926_, v___x_3945_);
lean_inc(v___x_3946_);
v___x_3947_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3946_);
lean_inc(v___x_3947_);
lean_inc(v___x_3936_);
v___x_3948_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3917_, v___x_3936_, v___x_3947_);
v___x_3949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38));
v___x_3950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_3951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3897_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40);
v___x_3953_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42));
v___x_3954_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3953_, v_currMacroScope_3876_);
v___x_3955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45));
v___x_3956_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3897_);
lean_ctor_set(v___x_3956_, 1, v___x_3952_);
lean_ctor_set(v___x_3956_, 2, v___x_3954_);
lean_ctor_set(v___x_3956_, 3, v___x_3955_);
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47));
v___x_3958_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49);
v___x_3959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50));
v___x_3960_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3959_, v_currMacroScope_3876_);
v___x_3961_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3897_);
lean_ctor_set(v___x_3961_, 1, v___x_3958_);
lean_ctor_set(v___x_3961_, 2, v___x_3960_);
lean_ctor_set(v___x_3961_, 3, v___x_3914_);
v___x_3962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52));
v___x_3963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_3964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3897_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54);
v___x_3966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55));
v___x_3967_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3966_, v_currMacroScope_3876_);
v___x_3968_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3897_);
lean_ctor_set(v___x_3968_, 1, v___x_3965_);
lean_ctor_set(v___x_3968_, 2, v___x_3967_);
lean_ctor_set(v___x_3968_, 3, v___x_3914_);
lean_inc_ref(v___x_3964_);
v___x_3969_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3962_, v___x_3964_, v___x_3968_);
lean_inc_ref_n(v___x_3951_, 2);
v___x_3970_ = l_Lean_Syntax_node5(v___x_3897_, v___x_3957_, v___x_3920_, v___x_3961_, v___x_3951_, v___x_3969_, v___x_3934_);
v___x_3971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57));
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_3973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3897_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
lean_inc_ref(v___x_3973_);
v___x_3974_ = l_Lean_Syntax_node3(v___x_3897_, v___x_3971_, v___x_3973_, v___x_3973_, v_type_3869_);
lean_inc(v___x_3974_);
v___x_3975_ = l_Lean_Syntax_node4(v___x_3897_, v___x_3884_, v___x_3970_, v_type_3869_, v___x_3974_, v___x_3924_);
v___x_3976_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_3956_, v___x_3975_);
v___x_3977_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60));
v___x_3978_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3977_, v___x_3900_, v___x_3900_);
lean_inc(v___x_3978_);
v___x_3979_ = l_Lean_Syntax_node4(v___x_3897_, v___x_3949_, v___x_3951_, v___x_3976_, v___x_3978_, v___x_3900_);
lean_inc_ref(v___x_3909_);
v___x_3980_ = l_Lean_Syntax_node5(v___x_3897_, v___x_3907_, v___x_3909_, v___x_3916_, v___x_3948_, v___x_3979_, v___x_3900_);
v___x_3981_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3898_, v___x_3906_, v___x_3980_);
v___x_3982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62));
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63));
v___x_3984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3897_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65));
v___x_3986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67));
v___x_3987_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3986_, v___x_3900_);
v___x_3988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70));
v___x_3989_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72);
v___x_3990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73));
v___x_3991_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_3990_, v_currMacroScope_3876_);
v___x_3992_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3897_);
lean_ctor_set(v___x_3992_, 1, v___x_3989_);
lean_ctor_set(v___x_3992_, 2, v___x_3991_);
lean_ctor_set(v___x_3992_, 3, v___x_3914_);
v___x_3993_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3915_);
v___x_3994_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3988_, v___x_3992_, v___x_3993_);
v___x_3995_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3985_, v___x_3987_, v___x_3994_);
v___x_3996_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3995_);
v___x_3997_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74));
v___x_3998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3897_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = l_Lean_Syntax_node3(v___x_3897_, v___x_3982_, v___x_3984_, v___x_3996_, v___x_3998_);
v___x_4000_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3999_);
v___x_4001_ = l_Lean_Syntax_node7(v___x_3897_, v___x_3899_, v___x_3900_, v___x_4000_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_);
v___x_4002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75));
v___x_4003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76));
v___x_4004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_3897_);
lean_ctor_set(v___x_4004_, 1, v___x_4002_);
v___x_4005_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78);
v___x_4006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79));
v___x_4007_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4006_, v_currMacroScope_3876_);
v___x_4008_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4008_, 0, v___x_3897_);
lean_ctor_set(v___x_4008_, 1, v___x_4005_);
lean_ctor_set(v___x_4008_, 2, v___x_4007_);
lean_ctor_set(v___x_4008_, 3, v___x_3914_);
lean_inc_ref(v___x_4008_);
v___x_4009_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3910_, v___x_4008_, v___x_3900_);
v___x_4010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81));
v___x_4011_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4010_, v___x_3936_, v___x_3946_);
v___x_4012_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4003_, v___x_4004_, v___x_4009_, v___x_4011_, v___x_3900_);
v___x_4013_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3898_, v___x_4001_, v___x_4012_);
if (lean_obj_tag(v_doc_x3f_3867_) == 1)
{
lean_object* v_val_4345_; lean_object* v___x_4346_; 
v_val_4345_ = lean_ctor_get(v_doc_x3f_3867_, 0);
lean_inc(v_val_4345_);
lean_dec_ref_known(v_doc_x3f_3867_, 1);
v___x_4346_ = l_Array_mkArray1___redArg(v_val_4345_);
v___y_4015_ = v___x_4346_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4347_; 
lean_dec(v_doc_x3f_3867_);
v___x_4347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268));
v___y_4015_ = v___x_4347_;
goto v___jp_4014_;
}
v___jp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4016_ = l_Array_append___redArg(v___x_3885_, v___y_4015_);
lean_dec_ref(v___y_4015_);
lean_inc_n(v___x_3897_, 183);
v___x_4017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4017_, 0, v___x_3897_);
lean_ctor_set(v___x_4017_, 1, v___x_3884_);
lean_ctor_set(v___x_4017_, 2, v___x_4016_);
lean_inc_ref_n(v___x_3900_, 57);
v___x_4018_ = l_Lean_Syntax_node7(v___x_3897_, v___x_3899_, v___x_4017_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_, v___x_3900_);
v___x_4019_ = lean_box(2);
v___x_4020_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82));
v___x_4021_ = lean_unsigned_to_nat(2u);
v___x_4022_ = lean_mk_empty_array_with_capacity(v___x_4021_);
v___x_4023_ = lean_array_push(v___x_4022_, v_elabName_3868_);
v___x_4024_ = lean_array_push(v___x_4023_, v___x_4020_);
v___x_4025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4019_);
lean_ctor_set(v___x_4025_, 1, v___x_3910_);
lean_ctor_set(v___x_4025_, 2, v___x_4024_);
v___x_4026_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84);
v___x_4027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85));
lean_inc_n(v_currMacroScope_3876_, 26);
lean_inc_n(v_quotContext_3875_, 26);
v___x_4028_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4027_, v_currMacroScope_3876_);
v___x_4029_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88));
v___x_4030_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4030_, 0, v___x_3897_);
lean_ctor_set(v___x_4030_, 1, v___x_4026_);
lean_ctor_set(v___x_4030_, 2, v___x_4028_);
lean_ctor_set(v___x_4030_, 3, v___x_4029_);
lean_inc_ref(v___x_4030_);
v___x_4031_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4030_);
v___x_4032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90);
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91));
v___x_4034_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4033_, v_currMacroScope_3876_);
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96));
v___x_4036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4036_, 0, v___x_3897_);
lean_ctor_set(v___x_4036_, 1, v___x_4032_);
lean_ctor_set(v___x_4036_, 2, v___x_4034_);
lean_ctor_set(v___x_4036_, 3, v___x_4035_);
lean_inc_ref(v___x_3926_);
v___x_4037_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_3926_, v___x_4036_);
lean_inc_ref_n(v___x_3934_, 3);
lean_inc(v___x_4031_);
lean_inc_ref_n(v___x_3920_, 2);
v___x_4038_ = l_Lean_Syntax_node5(v___x_3897_, v___x_3918_, v___x_3920_, v___x_4031_, v___x_4037_, v___x_3900_, v___x_3934_);
v___x_4039_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4038_);
v___x_4040_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v_monadName_3870_, v___x_3944_);
v___x_4041_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3937_, v___x_3926_, v___x_4040_);
v___x_4042_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4041_);
v___x_4043_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3917_, v___x_4039_, v___x_4042_);
v___x_4044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97));
v___x_4045_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98));
v___x_4046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_3897_);
lean_ctor_set(v___x_4046_, 1, v___x_4044_);
v___x_4047_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100));
v___x_4048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102));
v___x_4049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104));
v___x_4050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105));
v___x_4051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_3897_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107));
v___x_4053_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4052_, v___x_3900_);
v___x_4054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109));
v___x_4055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111));
v___x_4056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113));
v___x_4057_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4059_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4058_, v_currMacroScope_3876_);
v___x_4060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4060_, 0, v___x_3897_);
lean_ctor_set(v___x_4060_, 1, v___x_4057_);
lean_ctor_set(v___x_4060_, 2, v___x_4059_);
lean_ctor_set(v___x_4060_, 3, v___x_3914_);
lean_inc_ref(v___x_4060_);
v___x_4061_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4056_, v___x_4060_);
lean_inc_ref_n(v___x_3951_, 5);
v___x_4062_ = l_Lean_Syntax_node5(v___x_3897_, v___x_4055_, v___x_4061_, v___x_3900_, v___x_3900_, v___x_3951_, v_recover_3872_);
v___x_4063_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4054_, v___x_4062_);
lean_inc_n(v___x_4053_, 5);
lean_inc_ref_n(v___x_4051_, 5);
v___x_4064_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4049_, v___x_4051_, v___x_3900_, v___x_4053_, v___x_4063_);
v___x_4065_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4064_, v___x_3900_);
v___x_4066_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118);
v___x_4067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119));
v___x_4068_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4067_, v_currMacroScope_3876_);
v___x_4069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121));
v___x_4070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4070_, 0, v___x_3897_);
lean_ctor_set(v___x_4070_, 1, v___x_4066_);
lean_ctor_set(v___x_4070_, 2, v___x_4068_);
lean_ctor_set(v___x_4070_, 3, v___x_4069_);
lean_inc_ref(v___x_4070_);
v___x_4071_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4056_, v___x_4070_);
v___x_4072_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123);
v___x_4073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124));
v___x_4074_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4073_, v_currMacroScope_3876_);
v___x_4075_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127));
v___x_4076_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4076_, 0, v___x_3897_);
lean_ctor_set(v___x_4076_, 1, v___x_4072_);
lean_ctor_set(v___x_4076_, 2, v___x_4074_);
lean_ctor_set(v___x_4076_, 3, v___x_4075_);
v___x_4077_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129);
v___x_4078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130));
v___x_4079_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4078_, v_currMacroScope_3876_);
v___x_4080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4080_, 0, v___x_3897_);
lean_ctor_set(v___x_4080_, 1, v___x_4077_);
lean_ctor_set(v___x_4080_, 2, v___x_4079_);
lean_ctor_set(v___x_4080_, 3, v___x_3914_);
lean_inc_ref(v___x_4080_);
v___x_4081_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4056_, v___x_4080_);
v___x_4082_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132);
v___x_4083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133));
v___x_4084_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4083_, v_currMacroScope_3876_);
v___x_4085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136));
v___x_4086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4086_, 0, v___x_3897_);
lean_ctor_set(v___x_4086_, 1, v___x_4082_);
lean_ctor_set(v___x_4086_, 2, v___x_4084_);
lean_ctor_set(v___x_4086_, 3, v___x_4085_);
v___x_4087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4091_ = lean_box(0);
v___x_4092_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4091_, v_currMacroScope_3876_);
v___x_4093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4094_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4094_, 0, v___x_3897_);
lean_ctor_set(v___x_4094_, 1, v___x_4090_);
lean_ctor_set(v___x_4094_, 2, v___x_4092_);
lean_ctor_set(v___x_4094_, 3, v___x_4093_);
v___x_4095_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4089_, v___x_4094_);
v___x_4096_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4088_, v___x_3920_, v___x_4095_);
v___x_4097_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140);
v___x_4098_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141));
v___x_4099_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4098_, v_currMacroScope_3876_);
v___x_4100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144));
v___x_4101_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4101_, 0, v___x_3897_);
lean_ctor_set(v___x_4101_, 1, v___x_4097_);
lean_ctor_set(v___x_4101_, 2, v___x_4099_);
lean_ctor_set(v___x_4101_, 3, v___x_4100_);
v___x_4102_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4101_, v___x_4031_);
lean_inc(v___x_4096_);
v___x_4103_ = l_Lean_Syntax_node3(v___x_3897_, v___x_4087_, v___x_4096_, v___x_4102_, v___x_3934_);
v___x_4104_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4103_);
v___x_4105_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4086_, v___x_4104_);
v___x_4106_ = l_Lean_Syntax_node5(v___x_3897_, v___x_4055_, v___x_4081_, v___x_3900_, v___x_3900_, v___x_3951_, v___x_4105_);
v___x_4107_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4054_, v___x_4106_);
v___x_4108_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4049_, v___x_4051_, v___x_3900_, v___x_4053_, v___x_4107_);
v___x_4109_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4108_, v___x_3900_);
v___x_4110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146));
v___x_4111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147));
v___x_4112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_3897_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149));
v___x_4114_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151);
v___x_4115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153));
v___x_4116_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4115_, v_currMacroScope_3876_);
v___x_4117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4117_, 0, v___x_3897_);
lean_ctor_set(v___x_4117_, 1, v___x_4114_);
lean_ctor_set(v___x_4117_, 2, v___x_4116_);
lean_ctor_set(v___x_4117_, 3, v___x_3914_);
v___x_4118_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4113_, v___x_3900_, v___x_4117_);
v___x_4119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154));
v___x_4120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_3897_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156));
v___x_4122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157));
v___x_4123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_3897_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3896_);
lean_inc_ref(v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4121_, v___x_4123_, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4125_, v___x_3900_);
lean_inc(v___x_4126_);
v___x_4127_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4126_);
v___x_4128_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4127_);
lean_inc(v___x_4128_);
lean_inc_ref_n(v___x_4120_, 3);
lean_inc_ref_n(v___x_4112_, 3);
v___x_4129_ = l_Lean_Syntax_node6(v___x_3897_, v___x_4110_, v___x_4112_, v___x_4118_, v___x_4120_, v___x_4128_, v___x_3900_, v___x_3900_);
v___x_4130_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4129_, v___x_3900_);
v___x_4131_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159));
v___x_4132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160));
v___x_4133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_3897_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
v___x_4134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_3897_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4139_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169);
v___x_4140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170));
v___x_4141_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4140_, v_currMacroScope_3876_);
v___x_4142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174));
v___x_4143_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4143_, 0, v___x_3897_);
lean_ctor_set(v___x_4143_, 1, v___x_4139_);
lean_ctor_set(v___x_4143_, 2, v___x_4141_);
lean_ctor_set(v___x_4143_, 3, v___x_4142_);
v___x_4144_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4143_);
lean_inc_ref_n(v___x_4137_, 2);
v___x_4145_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4135_, v___x_4137_, v___x_4144_);
v___x_4146_ = l_Lean_Syntax_node3(v___x_3897_, v___x_4087_, v___x_4096_, v___x_4145_, v___x_3934_);
v___x_4147_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176);
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177));
v___x_4149_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4148_, v_currMacroScope_3876_);
v___x_4150_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4150_, 0, v___x_3897_);
lean_ctor_set(v___x_4150_, 1, v___x_4147_);
lean_ctor_set(v___x_4150_, 2, v___x_4149_);
lean_ctor_set(v___x_4150_, 3, v___x_3914_);
v___x_4151_ = l_Lean_Syntax_node3(v___x_3897_, v___x_4134_, v___x_4146_, v___x_3964_, v___x_4150_);
lean_inc_n(v___x_3974_, 3);
v___x_4152_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_3974_);
v___x_4153_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4151_, v___x_4152_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179));
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180));
v___x_4156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_3897_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182));
v___x_4158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183));
v___x_4159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_3897_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185));
v___x_4161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187));
v___x_4162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188));
v___x_4163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_3897_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4161_, v___x_4163_);
v___x_4165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189));
v___x_4166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_3897_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4161_, v___x_4166_);
lean_inc(v___x_4167_);
v___x_4168_ = l_Lean_Syntax_node3(v___x_3897_, v___x_4160_, v___x_4164_, v___x_3974_, v___x_4167_);
lean_inc_ref_n(v___x_4159_, 2);
v___x_4169_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4157_, v___x_4159_, v___x_4168_);
lean_inc_ref_n(v___x_4156_, 2);
v___x_4170_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4154_, v___x_4156_, v___x_4169_);
v___x_4171_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4170_);
v___x_4172_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4171_, v___x_3900_);
v___x_4173_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4172_);
v___x_4174_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4173_);
lean_inc_ref_n(v___x_4046_, 2);
v___x_4175_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4131_, v___x_4133_, v___x_4153_, v___x_4046_, v___x_4174_);
v___x_4176_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4175_, v___x_3900_);
v___x_4177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191);
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192));
v___x_4179_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4178_, v_currMacroScope_3876_);
v___x_4180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197));
v___x_4181_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4181_, 0, v___x_3897_);
lean_ctor_set(v___x_4181_, 1, v___x_4177_);
lean_ctor_set(v___x_4181_, 2, v___x_4179_);
lean_ctor_set(v___x_4181_, 3, v___x_4180_);
v___x_4182_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199);
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200));
v___x_4184_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4183_, v_currMacroScope_3876_);
v___x_4185_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4185_, 0, v___x_3897_);
lean_ctor_set(v___x_4185_, 1, v___x_4182_);
lean_ctor_set(v___x_4185_, 2, v___x_4184_);
lean_ctor_set(v___x_4185_, 3, v___x_3914_);
v___x_4186_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201);
v___x_4187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202));
v___x_4188_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4187_, v_currMacroScope_3876_);
v___x_4189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204));
v___x_4190_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4190_, 0, v___x_3897_);
lean_ctor_set(v___x_4190_, 1, v___x_4186_);
lean_ctor_set(v___x_4190_, 2, v___x_4188_);
lean_ctor_set(v___x_4190_, 3, v___x_4189_);
v___x_4191_ = l_Lean_Syntax_node5(v___x_3897_, v___x_3957_, v___x_3920_, v___x_4185_, v___x_3951_, v___x_4190_, v___x_3934_);
v___x_4192_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_4191_, v___x_3974_);
v___x_4193_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4181_, v___x_4192_);
v___x_4194_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4193_);
v___x_4195_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4194_, v___x_3900_);
v___x_4196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206));
v___x_4197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208));
v___x_4198_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210);
v___x_4199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211));
v___x_4200_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4199_, v_currMacroScope_3876_);
v___x_4201_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4201_, 0, v___x_3897_);
lean_ctor_set(v___x_4201_, 1, v___x_4198_);
lean_ctor_set(v___x_4201_, 2, v___x_4200_);
lean_ctor_set(v___x_4201_, 3, v___x_3914_);
v___x_4202_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213);
v___x_4203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214));
v___x_4204_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4203_, v_currMacroScope_3876_);
v___x_4205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219));
v___x_4206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4206_, 0, v___x_3897_);
lean_ctor_set(v___x_4206_, 1, v___x_4202_);
lean_ctor_set(v___x_4206_, 2, v___x_4204_);
lean_ctor_set(v___x_4206_, 3, v___x_4205_);
v___x_4207_ = l_Lean_Syntax_node3(v___x_3897_, v___x_3884_, v___x_4060_, v___x_3974_, v___x_4080_);
v___x_4208_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4206_, v___x_4207_);
v___x_4209_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4208_);
lean_inc_ref(v___x_4201_);
v___x_4210_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4197_, v___x_4201_, v___x_3900_, v___x_4137_, v___x_4209_);
v___x_4211_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4196_, v___x_4051_, v___x_3900_, v___x_4053_, v___x_4210_);
v___x_4212_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4211_, v___x_3900_);
v___x_4213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221);
v___x_4214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223));
v___x_4215_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4214_, v_currMacroScope_3876_);
v___x_4216_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4216_, 0, v___x_3897_);
lean_ctor_set(v___x_4216_, 1, v___x_4213_);
lean_ctor_set(v___x_4216_, 2, v___x_4215_);
lean_ctor_set(v___x_4216_, 3, v___x_3914_);
v___x_4217_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4113_, v___x_3900_, v___x_4216_);
v___x_4218_ = l_Lean_Syntax_node6(v___x_3897_, v___x_4110_, v___x_4112_, v___x_4217_, v___x_4120_, v___x_4128_, v___x_3900_, v___x_3900_);
v___x_4219_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4218_, v___x_3900_);
v___x_4220_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225);
v___x_4221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227));
v___x_4222_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4221_, v_currMacroScope_3876_);
v___x_4223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4223_, 0, v___x_3897_);
lean_ctor_set(v___x_4223_, 1, v___x_4220_);
lean_ctor_set(v___x_4223_, 2, v___x_4222_);
lean_ctor_set(v___x_4223_, 3, v___x_3914_);
v___x_4224_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4113_, v___x_3900_, v___x_4223_);
v___x_4225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228));
v___x_4226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_3897_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4161_, v___x_4226_);
v___x_4228_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4160_, v___x_4227_);
v___x_4229_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4157_, v___x_4159_, v___x_4228_);
v___x_4230_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4154_, v___x_4156_, v___x_4229_);
v___x_4231_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4230_);
v___x_4232_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4231_, v___x_3900_);
v___x_4233_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4232_);
v___x_4234_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4233_);
v___x_4235_ = l_Lean_Syntax_node6(v___x_3897_, v___x_4110_, v___x_4112_, v___x_4224_, v___x_4120_, v___x_4234_, v___x_3900_, v___x_3900_);
v___x_4236_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4235_, v___x_3900_);
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230));
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231));
v___x_4239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_3897_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233);
v___x_4241_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234));
v___x_4242_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4241_, v_currMacroScope_3876_);
v___x_4243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4243_, 0, v___x_3897_);
lean_ctor_set(v___x_4243_, 1, v___x_4240_);
lean_ctor_set(v___x_4243_, 2, v___x_4242_);
lean_ctor_set(v___x_4243_, 3, v___x_3914_);
v___x_4244_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4201_);
lean_inc(v___x_4244_);
v___x_4245_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4008_, v___x_4244_);
v___x_4246_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4245_);
lean_inc_ref(v___x_4243_);
v___x_4247_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4197_, v___x_4243_, v___x_3900_, v___x_4137_, v___x_4246_);
v___x_4248_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4196_, v___x_4051_, v___x_3900_, v___x_4053_, v___x_4247_);
v___x_4249_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4248_, v___x_3900_);
v___x_4250_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4243_);
v___x_4251_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4121_, v___x_4123_, v___x_4250_);
v___x_4252_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4251_, v___x_3900_);
v___x_4253_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_4249_, v___x_4252_);
v___x_4254_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4253_);
v___x_4255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236));
v___x_4256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237));
v___x_4257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_3897_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239);
v___x_4259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240));
v___x_4260_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4259_, v_currMacroScope_3876_);
v___x_4261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4261_, 0, v___x_3897_);
lean_ctor_set(v___x_4261_, 1, v___x_4258_);
lean_ctor_set(v___x_4261_, 2, v___x_4260_);
lean_ctor_set(v___x_4261_, 3, v___x_3914_);
v___x_4262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241));
v___x_4263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_3897_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243);
v___x_4265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244));
v___x_4266_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4265_, v_currMacroScope_3876_);
v___x_4267_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4267_, 0, v___x_3897_);
lean_ctor_set(v___x_4267_, 1, v___x_4264_);
lean_ctor_set(v___x_4267_, 2, v___x_4266_);
lean_ctor_set(v___x_4267_, 3, v___x_3914_);
lean_inc_ref_n(v___x_4267_, 2);
v___x_4268_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4056_, v___x_4267_);
v___x_4269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245));
v___x_4270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_3897_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4161_, v___x_4270_);
v___x_4272_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247);
v___x_4273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248));
v___x_4274_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4273_, v_currMacroScope_3876_);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251));
v___x_4276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4276_, 0, v___x_3897_);
lean_ctor_set(v___x_4276_, 1, v___x_4272_);
lean_ctor_set(v___x_4276_, 2, v___x_4274_);
lean_ctor_set(v___x_4276_, 3, v___x_4275_);
v___x_4277_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4276_, v___x_4244_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252));
v___x_4279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_3897_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4161_, v___x_4279_);
v___x_4281_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254);
v___x_4282_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256));
v___x_4283_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4282_, v_currMacroScope_3876_);
v___x_4284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4284_, 0, v___x_3897_);
lean_ctor_set(v___x_4284_, 1, v___x_4281_);
lean_ctor_set(v___x_4284_, 2, v___x_4283_);
lean_ctor_set(v___x_4284_, 3, v___x_3914_);
v___x_4285_ = l_Lean_Syntax_node5(v___x_3897_, v___x_4160_, v___x_4271_, v___x_4277_, v___x_4280_, v___x_4284_, v___x_4167_);
v___x_4286_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4157_, v___x_4159_, v___x_4285_);
v___x_4287_ = l_Lean_Syntax_node5(v___x_3897_, v___x_4055_, v___x_4268_, v___x_3900_, v___x_3900_, v___x_3951_, v___x_4286_);
v___x_4288_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4054_, v___x_4287_);
v___x_4289_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4049_, v___x_4051_, v___x_3900_, v___x_4053_, v___x_4288_);
v___x_4290_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4289_, v___x_3900_);
v___x_4291_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257);
v___x_4292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258));
v___x_4293_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4292_, v_currMacroScope_3876_);
v___x_4294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260));
v___x_4295_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4295_, 0, v___x_3897_);
lean_ctor_set(v___x_4295_, 1, v___x_4291_);
lean_ctor_set(v___x_4295_, 2, v___x_4293_);
lean_ctor_set(v___x_4295_, 3, v___x_4294_);
v___x_4296_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4113_, v___x_3900_, v___x_4295_);
v___x_4297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262);
v___x_4298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263));
v___x_4299_ = l_Lean_addMacroScope(v_quotContext_3875_, v___x_4298_, v_currMacroScope_3876_);
v___x_4300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266));
v___x_4301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4301_, 0, v___x_3897_);
lean_ctor_set(v___x_4301_, 1, v___x_4297_);
lean_ctor_set(v___x_4301_, 2, v___x_4299_);
lean_ctor_set(v___x_4301_, 3, v___x_4300_);
v___x_4302_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4267_);
v___x_4303_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4301_, v___x_4302_);
v___x_4304_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4303_);
v___x_4305_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4304_, v___x_3900_);
v___x_4306_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_4305_, v___x_4126_);
v___x_4307_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4306_);
v___x_4308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267));
v___x_4309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_3897_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4154_, v___x_4156_, v___x_4267_);
v___x_4311_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4310_);
v___x_4312_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4311_, v___x_3900_);
v___x_4313_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4312_);
v___x_4314_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_4309_, v___x_4314_);
v___x_4316_ = l_Lean_Syntax_node6(v___x_3897_, v___x_4110_, v___x_4112_, v___x_4296_, v___x_4120_, v___x_4307_, v___x_3900_, v___x_4315_);
v___x_4317_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4316_, v___x_3900_);
v___x_4318_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_4290_, v___x_4317_);
v___x_4319_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4318_);
v___x_4320_ = l_Lean_Syntax_node5(v___x_3897_, v___x_4255_, v___x_4257_, v___x_4261_, v___x_3900_, v___x_4263_, v___x_4319_);
v___x_4321_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4320_);
v___x_4322_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4237_, v___x_4239_, v___x_4254_, v___x_4321_, v___x_3900_);
v___x_4323_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4322_, v___x_3900_);
v___x_4324_ = l_Lean_Syntax_node8(v___x_3897_, v___x_3884_, v___x_4109_, v___x_4130_, v___x_4176_, v___x_4195_, v___x_4212_, v___x_4219_, v___x_4236_, v___x_4323_);
v___x_4325_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4324_);
v___x_4326_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4045_, v___x_4046_, v___x_4325_);
v___x_4327_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3884_, v___x_4030_, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v___x_4076_, v___x_4327_);
v___x_4329_ = l_Lean_Syntax_node5(v___x_3897_, v___x_4055_, v___x_4071_, v___x_3900_, v___x_3947_, v___x_3951_, v___x_4328_);
v___x_4330_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4054_, v___x_4329_);
v___x_4331_ = l_Lean_Syntax_node4(v___x_3897_, v___x_4049_, v___x_4051_, v___x_3900_, v___x_4053_, v___x_4330_);
v___x_4332_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4331_, v___x_3900_);
v___x_4333_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4138_, v___x_4070_);
v___x_4334_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4048_, v___x_4333_, v___x_3900_);
v___x_4335_ = l_Lean_Syntax_node3(v___x_3897_, v___x_3884_, v___x_4065_, v___x_4332_, v___x_4334_);
v___x_4336_ = l_Lean_Syntax_node1(v___x_3897_, v___x_4047_, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_node2(v___x_3897_, v___x_4045_, v___x_4046_, v___x_4336_);
v___x_4338_ = l_Lean_Syntax_node1(v___x_3897_, v___x_3884_, v___x_4337_);
v___x_4339_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3938_, v_adapt_3871_, v___x_4338_);
v___x_4340_ = l_Lean_Syntax_node4(v___x_3897_, v___x_3949_, v___x_3951_, v___x_4339_, v___x_3978_, v___x_3900_);
v___x_4341_ = l_Lean_Syntax_node5(v___x_3897_, v___x_3907_, v___x_3909_, v___x_4025_, v___x_4043_, v___x_4340_, v___x_3900_);
v___x_4342_ = l_Lean_Syntax_node2(v___x_3897_, v___x_3898_, v___x_4018_, v___x_4341_);
v___x_4343_ = l_Lean_Syntax_node3(v___x_3897_, v___x_3884_, v___x_3981_, v___x_4013_, v___x_4342_);
v___x_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
lean_ctor_set(v___x_4344_, 1, v_a_3874_);
return v___x_4344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___boxed(lean_object* v_doc_x3f_4348_, lean_object* v_elabName_4349_, lean_object* v_type_4350_, lean_object* v_monadName_4351_, lean_object* v_adapt_4352_, lean_object* v_recover_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v_doc_x3f_4348_, v_elabName_4349_, v_type_4350_, v_monadName_4351_, v_adapt_4352_, v_recover_4353_, v_a_4354_, v_a_4355_);
lean_dec_ref(v_a_4354_);
return v_res_4356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1(void){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0));
v___x_4401_ = l_String_toRawSubstring_x27(v___x_4400_);
return v___x_4401_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9(void){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8));
v___x_4421_ = l_Lean_mkCIdent(v___x_4420_);
return v___x_4421_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11));
v___x_4426_ = l_Lean_mkCIdent(v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(lean_object* v_x_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
lean_inc(v_x_4427_);
v___x_4431_ = l_Lean_Syntax_isOfKind(v_x_4427_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
lean_dec(v_x_4427_);
v___x_4432_ = lean_box(1);
v___x_4433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
lean_ctor_set(v___x_4433_, 1, v_a_4429_);
return v___x_4433_;
}
else
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v_elabName_4437_; lean_object* v___x_4438_; lean_object* v_type_4439_; lean_object* v___y_4441_; lean_object* v___x_4494_; 
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = l_Lean_Syntax_getArg(v_x_4427_, v___x_4434_);
v___x_4436_ = lean_unsigned_to_nat(2u);
v_elabName_4437_ = l_Lean_Syntax_getArg(v_x_4427_, v___x_4436_);
v___x_4438_ = lean_unsigned_to_nat(3u);
v_type_4439_ = l_Lean_Syntax_getArg(v_x_4427_, v___x_4438_);
lean_dec(v_x_4427_);
v___x_4494_ = l_Lean_Syntax_getOptional_x3f(v___x_4435_);
lean_dec(v___x_4435_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_box(0);
v___y_4441_ = v___x_4495_;
goto v___jp_4440_;
}
else
{
lean_object* v_val_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
v_val_4496_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4494_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_val_4496_);
lean_dec(v___x_4494_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_val_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
v___y_4441_ = v___x_4501_;
goto v___jp_4440_;
}
}
}
v___jp_4440_:
{
lean_object* v_quotContext_4442_; lean_object* v_currMacroScope_4443_; lean_object* v_ref_4444_; uint8_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v_a_4485_; lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
v_quotContext_4442_ = lean_ctor_get(v_a_4428_, 1);
v_currMacroScope_4443_ = lean_ctor_get(v_a_4428_, 2);
v_ref_4444_ = lean_ctor_get(v_a_4428_, 5);
v___x_4445_ = 0;
v___x_4446_ = l_Lean_SourceInfo_fromRef(v_ref_4444_, v___x_4445_);
v___x_4447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_4446_, 12);
v___x_4451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4446_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
v___x_4452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4453_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4454_ = lean_box(0);
lean_inc_n(v_currMacroScope_4443_, 3);
lean_inc_n(v_quotContext_4442_, 3);
v___x_4455_ = l_Lean_addMacroScope(v_quotContext_4442_, v___x_4454_, v_currMacroScope_4443_);
v___x_4456_ = lean_box(0);
v___x_4457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4458_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4446_);
lean_ctor_set(v___x_4458_, 1, v___x_4453_);
lean_ctor_set(v___x_4458_, 2, v___x_4455_);
lean_ctor_set(v___x_4458_, 3, v___x_4457_);
v___x_4459_ = l_Lean_Syntax_node1(v___x_4446_, v___x_4452_, v___x_4458_);
v___x_4460_ = l_Lean_Syntax_node2(v___x_4446_, v___x_4449_, v___x_4451_, v___x_4459_);
v___x_4461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4446_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4465_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1);
v___x_4466_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2));
v___x_4467_ = l_Lean_addMacroScope(v_quotContext_4442_, v___x_4466_, v_currMacroScope_4443_);
v___x_4468_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6));
v___x_4469_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4446_);
lean_ctor_set(v___x_4469_, 1, v___x_4465_);
lean_ctor_set(v___x_4469_, 2, v___x_4467_);
lean_ctor_set(v___x_4469_, 3, v___x_4468_);
v___x_4470_ = l_Lean_Syntax_node1(v___x_4446_, v___x_4464_, v___x_4469_);
v___x_4471_ = l_Lean_Syntax_node2(v___x_4446_, v___x_4461_, v___x_4463_, v___x_4470_);
v___x_4472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_4473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4446_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = l_Lean_Syntax_node3(v___x_4446_, v___x_4448_, v___x_4460_, v___x_4471_, v___x_4473_);
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_4476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4446_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4479_ = l_Lean_addMacroScope(v_quotContext_4442_, v___x_4478_, v_currMacroScope_4443_);
v___x_4480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4446_);
lean_ctor_set(v___x_4480_, 1, v___x_4477_);
lean_ctor_set(v___x_4480_, 2, v___x_4479_);
lean_ctor_set(v___x_4480_, 3, v___x_4456_);
v___x_4481_ = l_Lean_Syntax_node3(v___x_4446_, v___x_4447_, v___x_4474_, v___x_4476_, v___x_4480_);
v___x_4482_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9);
v___x_4483_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12);
v___x_4484_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4441_, v_elabName_4437_, v_type_4439_, v___x_4482_, v___x_4483_, v___x_4481_, v_a_4428_, v_a_4429_);
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_a_4486_ = lean_ctor_get(v___x_4484_, 1);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4484_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4485_);
lean_ctor_set(v_reuseFailAlloc_4492_, 1, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___boxed(lean_object* v_x_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(v_x_4504_, v_a_4505_, v_a_4506_);
lean_dec_ref(v_a_4505_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4514_ = lean_unsigned_to_nat(2u);
v___x_4515_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4513_, v___x_4514_, v_a_4509_, v_a_4510_, v_a_4511_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed(lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(v_a_4516_, v_a_4517_, v_a_4518_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
return v_res_4520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed), 4, 0);
v___x_4522_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1(){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4524_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
v___x_4525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0);
v___x_4526_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4524_, v___x_4525_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___boxed(lean_object* v_a_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
return v_res_4528_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1));
v___x_4562_ = l_Lean_mkCIdent(v___x_4561_);
return v___x_4562_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4));
v___x_4570_ = l_Lean_mkCIdent(v___x_4569_);
return v___x_4570_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18));
v___x_4572_ = l_Lean_mkCIdent(v___x_4571_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(lean_object* v_x_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4576_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
lean_inc(v_x_4573_);
v___x_4577_ = l_Lean_Syntax_isOfKind(v_x_4573_, v___x_4576_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
lean_dec(v_x_4573_);
v___x_4578_ = lean_box(1);
v___x_4579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
lean_ctor_set(v___x_4579_, 1, v_a_4575_);
return v___x_4579_;
}
else
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v_elabName_4583_; lean_object* v___x_4584_; lean_object* v_type_4585_; lean_object* v___y_4587_; lean_object* v___x_4601_; 
v___x_4580_ = lean_unsigned_to_nat(0u);
v___x_4581_ = l_Lean_Syntax_getArg(v_x_4573_, v___x_4580_);
v___x_4582_ = lean_unsigned_to_nat(2u);
v_elabName_4583_ = l_Lean_Syntax_getArg(v_x_4573_, v___x_4582_);
v___x_4584_ = lean_unsigned_to_nat(3u);
v_type_4585_ = l_Lean_Syntax_getArg(v_x_4573_, v___x_4584_);
lean_dec(v_x_4573_);
v___x_4601_ = l_Lean_Syntax_getOptional_x3f(v___x_4581_);
lean_dec(v___x_4581_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v___x_4602_; 
v___x_4602_ = lean_box(0);
v___y_4587_ = v___x_4602_;
goto v___jp_4586_;
}
else
{
lean_object* v_val_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
v_val_4603_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4601_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_val_4603_);
lean_dec(v___x_4601_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_val_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
v___y_4587_ = v___x_4608_;
goto v___jp_4586_;
}
}
}
v___jp_4586_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v_a_4592_; lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
v___x_4588_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2);
v___x_4589_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5);
v___x_4590_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6);
v___x_4591_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4587_, v_elabName_4583_, v_type_4585_, v___x_4588_, v___x_4589_, v___x_4590_, v_a_4574_, v_a_4575_);
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_a_4593_ = lean_ctor_get(v___x_4591_, 1);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4591_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4592_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___boxed(lean_object* v_x_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(v_x_4611_, v_a_4612_, v_a_4613_);
lean_dec_ref(v_a_4612_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4620_ = lean_unsigned_to_nat(2u);
v___x_4621_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4619_, v___x_4620_, v_a_4615_, v_a_4616_, v_a_4617_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed(lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
return v_res_4626_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed), 4, 0);
v___x_4628_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4628_, 0, v___x_4627_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
v___x_4631_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0);
v___x_4632_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4630_, v___x_4631_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___boxed(lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
return v_res_4634_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_MissingDocs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Config(builtin);
}
#ifdef __cplusplus
}
#endif
