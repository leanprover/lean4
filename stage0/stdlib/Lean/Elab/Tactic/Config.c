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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
lean_ctor_set(v___x_355_, 4, v___x_353_);
lean_ctor_set(v___x_355_, 5, v___x_353_);
lean_ctor_set(v___x_355_, 6, v___x_353_);
lean_ctor_set(v___x_355_, 7, v___x_353_);
lean_ctor_set(v___x_355_, 8, v___x_353_);
lean_ctor_set(v___x_355_, 9, v___x_353_);
lean_ctor_set(v___x_355_, 10, v___x_353_);
lean_ctor_set(v___x_355_, 11, v___x_352_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_unsigned_to_nat(32u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_359_ = ((size_t)5ULL);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_unsigned_to_nat(32u);
v___x_362_ = lean_mk_empty_array_with_capacity(v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_364_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_360_);
lean_ctor_set(v___x_364_, 3, v___x_360_);
lean_ctor_set_usize(v___x_364_, 4, v___x_359_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_box(1);
v___x_366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
lean_ctor_set(v___x_368_, 2, v___x_365_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_390_, lean_object* v_declHint_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_env_396_; uint8_t v___x_397_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_st_ref_get(v___y_392_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
v___x_397_ = l_Lean_Name_isAnonymous(v_declHint_391_);
if (v___x_397_ == 0)
{
uint8_t v_isExporting_398_; 
v_isExporting_398_ = lean_ctor_get_uint8(v_env_396_, sizeof(void*)*13);
if (v_isExporting_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v_env_396_);
lean_dec(v_declHint_391_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_msg_390_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; uint8_t v___x_401_; 
lean_inc_ref(v_env_396_);
v___x_400_ = l_Lean_Environment_setExporting(v_env_396_, v___x_397_);
lean_inc(v_declHint_391_);
lean_inc_ref(v___x_400_);
v___x_401_ = l_Lean_Environment_contains(v___x_400_, v_declHint_391_, v_isExporting_398_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec_ref(v___x_400_);
lean_dec_ref(v_env_396_);
lean_dec(v_declHint_391_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_msg_390_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_c_408_; lean_object* v___x_409_; 
v___x_403_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_404_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_405_ = l_Lean_Options_empty;
v___x_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_406_, 0, v___x_400_);
lean_ctor_set(v___x_406_, 1, v___x_403_);
lean_ctor_set(v___x_406_, 2, v___x_404_);
lean_ctor_set(v___x_406_, 3, v___x_405_);
lean_inc(v_declHint_391_);
v___x_407_ = l_Lean_MessageData_ofConstName(v_declHint_391_, v___x_397_);
v_c_408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_408_, 0, v___x_406_);
lean_ctor_set(v_c_408_, 1, v___x_407_);
v___x_409_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_396_, v_declHint_391_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec_ref(v_env_396_);
lean_dec(v_declHint_391_);
v___x_410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_c_408_);
v___x_412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_MessageData_note(v___x_413_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v_msg_390_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
else
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_451_; 
v_val_417_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_451_ == 0)
{
v___x_419_ = v___x_409_;
v_isShared_420_ = v_isSharedCheck_451_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v___x_409_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_451_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_mod_423_; uint8_t v___x_424_; 
v___x_421_ = l_Lean_Environment_header(v_env_396_);
lean_dec_ref(v_env_396_);
v___x_422_ = l_Lean_EnvironmentHeader_moduleNames(v___x_421_);
v_mod_423_ = lean_array_get(v___x_394_, v___x_422_, v_val_417_);
lean_dec(v_val_417_);
lean_dec_ref(v___x_422_);
v___x_424_ = l_Lean_isPrivateName(v_declHint_391_);
lean_dec(v_declHint_391_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_425_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_c_408_);
v___x_427_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_MessageData_ofName(v_mod_423_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_MessageData_note(v___x_432_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v_msg_390_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 0);
lean_ctor_set(v___x_419_, 0, v___x_434_);
v___x_436_ = v___x_419_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_438_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_c_408_);
v___x_440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_MessageData_ofName(v_mod_423_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_MessageData_note(v___x_445_);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v_msg_390_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 0);
lean_ctor_set(v___x_419_, 0, v___x_447_);
v___x_449_ = v___x_419_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_452_; 
lean_dec_ref(v_env_396_);
lean_dec(v_declHint_391_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_msg_390_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_453_, lean_object* v_declHint_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_453_, v_declHint_454_, v___y_455_);
lean_dec(v___y_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_458_, lean_object* v_declHint_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v___x_465_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_458_, v_declHint_459_, v___y_463_);
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = l_Lean_unknownIdentifierMessageTag;
v___x_471_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_a_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_476_, lean_object* v_declHint_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_476_, v_declHint_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_484_, lean_object* v_msg_485_, lean_object* v_declHint_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_494_; 
v___x_492_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_485_, v_declHint_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v___x_492_);
v___x_494_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_484_, v_a_493_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_495_, lean_object* v_msg_496_, lean_object* v_declHint_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_495_, v_msg_496_, v_declHint_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v_ref_495_);
return v_res_503_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_507_, lean_object* v_constName_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_514_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_515_ = 0;
lean_inc(v_constName_508_);
v___x_516_ = l_Lean_MessageData_ofConstName(v_constName_508_, v___x_515_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_514_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_507_, v___x_519_, v_constName_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_521_, lean_object* v_constName_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_521_, v_constName_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v_ref_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(lean_object* v_constName_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_ref_535_; lean_object* v___x_536_; 
v_ref_535_ = lean_ctor_get(v___y_532_, 2);
v___x_536_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_535_, v_constName_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg___boxed(lean_object* v_constName_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(lean_object* v_constName_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; lean_object* v_env_551_; uint8_t v___x_552_; lean_object* v___x_553_; 
v___x_550_ = lean_st_ref_get(v___y_548_);
v_env_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc_ref(v_env_551_);
lean_dec(v___x_550_);
v___x_552_ = 0;
lean_inc(v_constName_544_);
v___x_553_ = l_Lean_Environment_find_x3f(v_env_551_, v_constName_544_, v___x_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_constName_544_);
v_val_555_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_553_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v___x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_val_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0___boxed(lean_object* v_constName_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_constName_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(lean_object* v_structName_573_, lean_object* v_field_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
if (lean_obj_tag(v_field_574_) == 1)
{
lean_object* v_pre_580_; 
v_pre_580_ = lean_ctor_get(v_field_574_, 0);
if (lean_obj_tag(v_pre_580_) == 0)
{
lean_object* v_str_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_str_581_ = lean_ctor_get(v_field_574_, 1);
lean_inc_ref(v_str_581_);
lean_dec_ref_known(v_field_574_, 2);
v___x_582_ = lean_box(0);
v___x_583_ = l_Lean_Name_str___override(v___x_582_, v_str_581_);
v___x_584_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_573_, v___x_583_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v___x_584_;
}
else
{
lean_object* v_str_585_; lean_object* v___x_586_; 
lean_inc(v_pre_580_);
v_str_585_ = lean_ctor_get(v_field_574_, 1);
lean_inc_ref(v_str_585_);
lean_dec_ref_known(v_field_574_, 2);
lean_inc(v_structName_573_);
v___x_586_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_573_, v_pre_580_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_590_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v_fst_588_ = lean_ctor_get(v_a_587_, 0);
lean_inc(v_fst_588_);
v_snd_589_ = lean_ctor_get(v_a_587_, 1);
lean_inc(v_snd_589_);
lean_dec(v_a_587_);
v___x_590_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_snd_589_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = l_Lean_ConstantInfo_type(v_a_591_);
lean_dec(v_a_591_);
v___x_593_ = l_Lean_Expr_getForallBody(v___x_592_);
lean_dec_ref(v___x_592_);
if (lean_obj_tag(v___x_593_) == 4)
{
lean_object* v_declName_594_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___x_621_; lean_object* v_env_622_; uint8_t v___x_623_; 
v_declName_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc_n(v_declName_594_, 2);
lean_dec_ref_known(v___x_593_, 2);
v___x_621_ = lean_st_ref_get(v_a_578_);
v_env_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_621_);
v___x_623_ = l_Lean_isStructure(v_env_622_, v_declName_594_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
lean_inc(v_fst_588_);
v___x_624_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_588_, v_structName_573_, lean_box(0), v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref_known(v___x_624_, 1);
v___y_596_ = v_a_575_;
v___y_597_ = v_a_576_;
v___y_598_ = v_a_577_;
v___y_599_ = v_a_578_;
goto v___jp_595_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_declName_594_);
lean_dec(v_fst_588_);
lean_dec_ref(v_str_585_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_dec(v_structName_573_);
v___y_596_ = v_a_575_;
v___y_597_ = v_a_576_;
v___y_598_ = v_a_577_;
v___y_599_ = v_a_578_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = l_Lean_Name_str___override(v___x_600_, v_str_585_);
v___x_602_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_declName_594_, v___x_601_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_620_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_620_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_620_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_620_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_619_; 
v_fst_607_ = lean_ctor_get(v_a_603_, 0);
v_snd_608_ = lean_ctor_get(v_a_603_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_619_ == 0)
{
v___x_610_ = v_a_603_;
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snd_608_);
lean_inc(v_fst_607_);
lean_dec(v_a_603_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_Name_append(v_fst_588_, v_fst_607_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_608_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_614_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
else
{
lean_dec(v_fst_588_);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_633_; 
lean_dec_ref(v___x_593_);
lean_dec_ref(v_str_585_);
v___x_633_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_588_, v_structName_573_, lean_box(0), v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v___x_633_;
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_fst_588_);
lean_dec_ref(v_str_585_);
lean_dec(v_structName_573_);
v_a_634_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_590_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_590_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_dec_ref(v_str_585_);
lean_dec(v_structName_573_);
return v___x_586_;
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v_field_574_);
lean_dec(v_structName_573_);
v___x_642_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1);
v___x_643_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_642_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___boxed(lean_object* v_structName_644_, lean_object* v_field_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_644_, v_field_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(lean_object* v_00_u03b1_652_, lean_object* v_constName_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___boxed(lean_object* v_00_u03b1_660_, lean_object* v_constName_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(v_00_u03b1_660_, v_constName_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_668_, lean_object* v_ref_669_, lean_object* v_constName_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_669_, v_constName_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_677_, lean_object* v_ref_678_, lean_object* v_constName_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(v_00_u03b1_677_, v_ref_678_, v_constName_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v_ref_678_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_686_, lean_object* v_ref_687_, lean_object* v_msg_688_, lean_object* v_declHint_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_687_, v_msg_688_, v_declHint_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_696_, lean_object* v_ref_697_, lean_object* v_msg_698_, lean_object* v_declHint_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_696_, v_ref_697_, v_msg_698_, v_declHint_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_ref_697_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_706_, lean_object* v_declHint_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_706_, v_declHint_707_, v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_714_, lean_object* v_declHint_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_714_, v_declHint_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_722_, lean_object* v_ref_723_, lean_object* v_msg_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_723_, v_msg_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_731_, lean_object* v_ref_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_731_, v_ref_732_, v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v_ref_732_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(lean_object* v_e_740_, lean_object* v___y_741_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = l_Lean_Expr_hasMVar(v_e_740_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_e_740_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v_mctx_746_; lean_object* v___x_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; lean_object* v___x_750_; lean_object* v_cache_751_; lean_object* v_zetaDeltaFVarIds_752_; lean_object* v_postponed_753_; lean_object* v_diag_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_763_; 
v___x_745_ = lean_st_ref_get(v___y_741_);
v_mctx_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_mctx_746_);
lean_dec(v___x_745_);
v___x_747_ = l_Lean_instantiateMVarsCore(v_mctx_746_, v_e_740_);
v_fst_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_fst_748_);
v_snd_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc(v_snd_749_);
lean_dec_ref(v___x_747_);
v___x_750_ = lean_st_ref_take(v___y_741_);
v_cache_751_ = lean_ctor_get(v___x_750_, 1);
v_zetaDeltaFVarIds_752_ = lean_ctor_get(v___x_750_, 2);
v_postponed_753_ = lean_ctor_get(v___x_750_, 3);
v_diag_754_ = lean_ctor_get(v___x_750_, 4);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_764_);
v___x_756_ = v___x_750_;
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_diag_754_);
lean_inc(v_postponed_753_);
lean_inc(v_zetaDeltaFVarIds_752_);
lean_inc(v_cache_751_);
lean_dec(v___x_750_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_snd_749_);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_snd_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_cache_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_zetaDeltaFVarIds_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_postponed_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_diag_754_);
v___x_759_ = v_reuseFailAlloc_762_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_st_ref_put(v___y_741_, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_fst_748_);
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg___boxed(lean_object* v_e_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_765_, v___y_766_);
lean_dec(v___y_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(lean_object* v_e_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_769_, v___y_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___boxed(lean_object* v_e_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(v_e_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
v___x_795_ = lean_apply_7(v_x_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, lean_box(0));
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed(lean_object* v_x_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(v_x_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(lean_object* v_lctx_805_, lean_object* v_localInsts_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___f_815_; lean_object* v___x_816_; 
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_815_, 0, v_x_807_);
lean_closure_set(v___f_815_, 1, v___y_808_);
lean_closure_set(v___f_815_, 2, v___y_809_);
v___x_816_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_805_, v_localInsts_806_, v___f_815_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_816_) == 0)
{
return v___x_816_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___boxed(lean_object* v_lctx_825_, lean_object* v_localInsts_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_825_, v_localInsts_826_, v_x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(lean_object* v_00_u03b1_836_, lean_object* v_lctx_837_, lean_object* v_localInsts_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_837_, v_localInsts_838_, v_x_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed(lean_object* v_00_u03b1_848_, lean_object* v_lctx_849_, lean_object* v_localInsts_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(v_00_u03b1_848_, v_lctx_849_, v_localInsts_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl(lean_box(0), v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_868_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_868_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg___boxed(lean_object* v_x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(lean_object* v_00_u03b1_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___boxed(lean_object* v_00_u03b1_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(v_00_u03b1_904_, v_x_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_913_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6(void){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Array_mkArray0___redArg();
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(lean_object* v_structName_942_, lean_object* v_source_x3f_943_, lean_object* v_fields_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
if (lean_obj_tag(v_source_x3f_943_) == 0)
{
lean_object* v_ref_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_ref_952_ = lean_ctor_get(v___y_949_, 2);
v___x_953_ = 0;
v___x_954_ = l_Lean_SourceInfo_fromRef(v_ref_952_, v___x_953_);
v___x_955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_954_, 8);
v___x_957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_954_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_959_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_960_, 0, v___x_954_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_963_ = l_Lean_Syntax_SepArray_ofElems(v___x_962_, v_fields_944_);
v___x_964_ = l_Array_append___redArg(v___x_959_, v___x_963_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_954_);
lean_ctor_set(v___x_965_, 1, v___x_958_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
v___x_966_ = l_Lean_Syntax_node1(v___x_954_, v___x_961_, v___x_965_);
v___x_967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_960_);
v___x_968_ = l_Lean_Syntax_node1(v___x_954_, v___x_967_, v___x_960_);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_954_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_mkCIdent(v_structName_942_);
v___x_972_ = l_Lean_Syntax_node2(v___x_954_, v___x_958_, v___x_970_, v___x_971_);
v___x_973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_954_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_Syntax_node6(v___x_954_, v___x_955_, v___x_957_, v___x_960_, v___x_966_, v___x_968_, v___x_972_, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
else
{
lean_object* v_val_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1012_; 
v_val_977_ = lean_ctor_get(v_source_x3f_943_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_source_x3f_943_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_979_ = v_source_x3f_943_;
v_isShared_980_ = v_isSharedCheck_1012_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_val_977_);
lean_dec(v_source_x3f_943_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1012_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_ref_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v_ref_981_ = lean_ctor_get(v___y_949_, 2);
v___x_982_ = 0;
v___x_983_ = l_Lean_SourceInfo_fromRef(v_ref_981_, v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_983_, 11);
v___x_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_983_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_988_ = l_Lean_Syntax_node1(v___x_983_, v___x_987_, v_val_977_);
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_983_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Syntax_node2(v___x_983_, v___x_987_, v___x_988_, v___x_990_);
v___x_992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_993_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_995_ = l_Lean_Syntax_SepArray_ofElems(v___x_994_, v_fields_944_);
v___x_996_ = l_Array_append___redArg(v___x_993_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_997_, 0, v___x_983_);
lean_ctor_set(v___x_997_, 1, v___x_987_);
lean_ctor_set(v___x_997_, 2, v___x_996_);
v___x_998_ = l_Lean_Syntax_node1(v___x_983_, v___x_992_, v___x_997_);
v___x_999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_983_);
lean_ctor_set(v___x_1000_, 1, v___x_987_);
lean_ctor_set(v___x_1000_, 2, v___x_993_);
v___x_1001_ = l_Lean_Syntax_node1(v___x_983_, v___x_999_, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_983_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_mkCIdent(v_structName_942_);
v___x_1005_ = l_Lean_Syntax_node2(v___x_983_, v___x_987_, v___x_1003_, v___x_1004_);
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_983_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node6(v___x_983_, v___x_984_, v___x_986_, v___x_991_, v___x_998_, v___x_1001_, v___x_1005_, v___x_1007_);
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 0);
lean_ctor_set(v___x_979_, 0, v___x_1008_);
v___x_1010_ = v___x_979_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed(lean_object* v_structName_1013_, lean_object* v_source_x3f_1014_, lean_object* v_fields_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_1013_, v_source_x3f_1014_, v_fields_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v_fields_1015_);
return v_res_1023_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_1041_ = l_String_toRawSubstring_x27(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(lean_object* v_a_1091_, lean_object* v_structName_1092_, lean_object* v_____r_1093_, lean_object* v_source_x3f_1094_, lean_object* v_seenFields_1095_, lean_object* v_fields_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_toCold_1104_; lean_object* v_value_1105_; lean_object* v_ref_1106_; lean_object* v_quotContext_1107_; lean_object* v_currMacroScope_1108_; lean_object* v_ref_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_toCold_1104_ = lean_ctor_get(v___y_1101_, 0);
v_value_1105_ = lean_ctor_get(v_a_1091_, 2);
lean_inc(v_value_1105_);
lean_dec_ref(v_a_1091_);
v_ref_1106_ = lean_ctor_get(v___y_1101_, 2);
v_quotContext_1107_ = lean_ctor_get(v_toCold_1104_, 8);
v_currMacroScope_1108_ = lean_ctor_get(v_toCold_1104_, 9);
v_ref_1109_ = l_Lean_replaceRef(v_value_1105_, v_ref_1106_);
v___x_1110_ = 0;
v___x_1111_ = l_Lean_SourceInfo_fromRef(v_ref_1109_, v___x_1110_);
lean_dec(v_ref_1109_);
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1));
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_1111_, 8);
v___x_1115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1111_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_1117_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_1118_ = lean_box(0);
lean_inc(v_currMacroScope_1108_);
lean_inc(v_quotContext_1107_);
v___x_1119_ = l_Lean_addMacroScope(v_quotContext_1107_, v___x_1118_, v_currMacroScope_1108_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_1121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1111_);
lean_ctor_set(v___x_1121_, 1, v___x_1117_);
lean_ctor_set(v___x_1121_, 2, v___x_1119_);
lean_ctor_set(v___x_1121_, 3, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node1(v___x_1111_, v___x_1116_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node2(v___x_1111_, v___x_1113_, v___x_1115_, v___x_1122_);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1111_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_1127_ = l_Lean_mkCIdent(v_structName_1092_);
lean_inc(v___x_1127_);
v___x_1128_ = l_Lean_Syntax_node1(v___x_1111_, v___x_1126_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1111_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
lean_inc_ref(v___x_1125_);
v___x_1131_ = l_Lean_Syntax_node5(v___x_1111_, v___x_1112_, v___x_1123_, v_value_1105_, v___x_1125_, v___x_1128_, v___x_1130_);
if (lean_obj_tag(v_source_x3f_1094_) == 1)
{
lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1163_; 
v_val_1132_ = lean_ctor_get(v_source_x3f_1094_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_source_x3f_1094_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1134_ = v_source_x3f_1094_;
v_isShared_1135_ = v_isSharedCheck_1163_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_dec(v_source_x3f_1094_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1163_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_1111_, 10);
v___x_1138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1111_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27));
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1111_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_node3(v___x_1111_, v___x_1126_, v___x_1131_, v___x_1140_, v_val_1132_);
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1111_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_Syntax_node2(v___x_1111_, v___x_1126_, v___x_1141_, v___x_1143_);
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_1146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_1147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1111_);
lean_ctor_set(v___x_1147_, 1, v___x_1126_);
lean_ctor_set(v___x_1147_, 2, v___x_1146_);
lean_inc_ref(v___x_1147_);
v___x_1148_ = l_Lean_Syntax_node1(v___x_1111_, v___x_1145_, v___x_1147_);
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1150_ = l_Lean_Syntax_node1(v___x_1111_, v___x_1149_, v___x_1147_);
v___x_1151_ = l_Lean_Syntax_node2(v___x_1111_, v___x_1126_, v___x_1125_, v___x_1127_);
v___x_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1111_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_Syntax_node6(v___x_1111_, v___x_1136_, v___x_1138_, v___x_1144_, v___x_1148_, v___x_1150_, v___x_1151_, v___x_1153_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1154_);
v___x_1156_ = v___x_1134_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_seenFields_1095_);
lean_ctor_set(v___x_1158_, 1, v_fields_1096_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1156_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v___x_1127_);
lean_dec_ref_known(v___x_1125_, 2);
lean_dec(v___x_1111_);
lean_dec(v_source_x3f_1094_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1131_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_seenFields_1095_);
lean_ctor_set(v___x_1166_, 1, v_fields_1096_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1164_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1165_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___boxed(lean_object* v_a_1170_, lean_object* v_structName_1171_, lean_object* v_____r_1172_, lean_object* v_source_x3f_1173_, lean_object* v_seenFields_1174_, lean_object* v_fields_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_1170_, v_structName_1171_, v_____r_1172_, v_source_x3f_1173_, v_seenFields_1174_, v_fields_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(lean_object* v_opts_1184_, lean_object* v_opt_1185_){
_start:
{
lean_object* v_name_1186_; lean_object* v_defValue_1187_; lean_object* v_map_1188_; lean_object* v___x_1189_; 
v_name_1186_ = lean_ctor_get(v_opt_1185_, 0);
v_defValue_1187_ = lean_ctor_get(v_opt_1185_, 1);
v_map_1188_ = lean_ctor_get(v_opts_1184_, 0);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1188_, v_name_1186_);
if (lean_obj_tag(v___x_1189_) == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_unbox(v_defValue_1187_);
return v___x_1190_;
}
else
{
lean_object* v_val_1191_; 
v_val_1191_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v___x_1189_, 1);
if (lean_obj_tag(v_val_1191_) == 1)
{
uint8_t v_v_1192_; 
v_v_1192_ = lean_ctor_get_uint8(v_val_1191_, 0);
lean_dec_ref_known(v_val_1191_, 0);
return v_v_1192_;
}
else
{
uint8_t v___x_1193_; 
lean_dec(v_val_1191_);
v___x_1193_ = lean_unbox(v_defValue_1187_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_opts_1194_, lean_object* v_opt_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_opts_1194_, v_opt_1195_);
lean_dec_ref(v_opt_1195_);
lean_dec_ref(v_opts_1194_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_box(1);
v___x_1199_ = l_Lean_MessageData_ofFormat(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2));
v___x_1204_ = l_Lean_MessageData_ofFormat(v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
return v_x_1205_;
}
else
{
lean_object* v_head_1207_; lean_object* v_tail_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1230_; 
v_head_1207_ = lean_ctor_get(v_x_1206_, 0);
v_tail_1208_ = lean_ctor_get(v_x_1206_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1206_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1210_ = v_x_1206_;
v_isShared_1211_ = v_isSharedCheck_1230_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_tail_1208_);
lean_inc(v_head_1207_);
lean_dec(v_x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1230_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_before_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1228_; 
v_before_1212_ = lean_ctor_get(v_head_1207_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_head_1207_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_head_1207_, 1);
lean_dec(v_unused_1229_);
v___x_1214_ = v_head_1207_;
v_isShared_1215_ = v_isSharedCheck_1228_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_before_1212_);
lean_dec(v_head_1207_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1228_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 7);
lean_ctor_set(v___x_1214_, 1, v___x_1216_);
lean_ctor_set(v___x_1214_, 0, v_x_1205_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_x_1205_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 7);
lean_ctor_set(v___x_1210_, 1, v___x_1219_);
lean_ctor_set(v___x_1210_, 0, v___x_1218_);
v___x_1221_ = v___x_1210_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_MessageData_ofSyntax(v_before_1212_);
v___x_1223_ = l_Lean_indentD(v___x_1222_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1221_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v_x_1205_ = v___x_1224_;
v_x_1206_ = v_tail_1208_;
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
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1));
v___x_1235_ = l_Lean_MessageData_ofFormat(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(lean_object* v_msgData_1236_, lean_object* v_macroStack_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1238_);
v___x_1241_ = l_Lean_Elab_pp_macroStack;
v___x_1242_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v___x_1240_, v___x_1241_);
lean_dec_ref(v___x_1240_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec(v_macroStack_1237_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_msgData_1236_);
return v___x_1243_;
}
else
{
if (lean_obj_tag(v_macroStack_1237_) == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_msgData_1236_);
return v___x_1244_;
}
else
{
lean_object* v_head_1245_; lean_object* v_after_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1261_; 
v_head_1245_ = lean_ctor_get(v_macroStack_1237_, 0);
lean_inc(v_head_1245_);
v_after_1246_ = lean_ctor_get(v_head_1245_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_head_1245_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v_head_1245_, 0);
lean_dec(v_unused_1262_);
v___x_1248_ = v_head_1245_;
v_isShared_1249_ = v_isSharedCheck_1261_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_after_1246_);
lean_dec(v_head_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1261_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 7);
lean_ctor_set(v___x_1248_, 1, v___x_1250_);
lean_ctor_set(v___x_1248_, 0, v_msgData_1236_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_msgData_1236_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_msgData_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1253_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_MessageData_ofSyntax(v_after_1246_);
v___x_1256_ = l_Lean_indentD(v___x_1255_);
v_msgData_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1257_, 0, v___x_1254_);
lean_ctor_set(v_msgData_1257_, 1, v___x_1256_);
v___x_1258_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(v_msgData_1257_, v_macroStack_1237_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___boxed(lean_object* v_msgData_1263_, lean_object* v_macroStack_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_1263_, v_macroStack_1264_, v___y_1265_);
lean_dec_ref(v___y_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_ref_1276_; lean_object* v_macroStack_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1290_; 
v_ref_1276_ = lean_ctor_get(v___y_1273_, 2);
v_macroStack_1277_ = lean_ctor_get(v___y_1269_, 1);
v___x_1278_ = l_Lean_Elab_getBetterRef(v_ref_1276_, v_macroStack_1277_);
v___x_1279_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_1268_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
lean_inc(v_macroStack_1277_);
v___x_1281_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_a_1280_, v_macroStack_1277_, v___y_1273_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1278_);
lean_ctor_set(v___x_1286_, 1, v_a_1282_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg___boxed(lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(lean_object* v_ref_1300_, lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_toCold_1309_; lean_object* v_currRecDepth_1310_; lean_object* v_ref_1311_; uint16_t v_optionFlags_1312_; uint8_t v_suppressElabErrors_1313_; uint8_t v_isRecordingDeps_1314_; lean_object* v_ref_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_toCold_1309_ = lean_ctor_get(v___y_1306_, 0);
v_currRecDepth_1310_ = lean_ctor_get(v___y_1306_, 1);
v_ref_1311_ = lean_ctor_get(v___y_1306_, 2);
v_optionFlags_1312_ = lean_ctor_get_uint16(v___y_1306_, sizeof(void*)*3);
v_suppressElabErrors_1313_ = lean_ctor_get_uint8(v___y_1306_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1314_ = lean_ctor_get_uint8(v___y_1306_, sizeof(void*)*3 + 3);
v_ref_1315_ = l_Lean_replaceRef(v_ref_1300_, v_ref_1311_);
lean_inc(v_currRecDepth_1310_);
lean_inc_ref(v_toCold_1309_);
v___x_1316_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1316_, 0, v_toCold_1309_);
lean_ctor_set(v___x_1316_, 1, v_currRecDepth_1310_);
lean_ctor_set(v___x_1316_, 2, v_ref_1315_);
lean_ctor_set_uint16(v___x_1316_, sizeof(void*)*3, v_optionFlags_1312_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*3 + 2, v_suppressElabErrors_1313_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*3 + 3, v_isRecordingDeps_1314_);
v___x_1317_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___x_1316_, v___y_1307_);
lean_dec_ref_known(v___x_1316_, 3);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg___boxed(lean_object* v_ref_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1318_, v_msg_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v_ref_1318_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(lean_object* v_msg_1328_, lean_object* v_declHint_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_env_1334_; uint8_t v___x_1335_; 
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_st_ref_get(v___y_1330_);
v_env_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc_ref(v_env_1334_);
lean_dec(v___x_1333_);
v___x_1335_ = l_Lean_Name_isAnonymous(v_declHint_1329_);
if (v___x_1335_ == 0)
{
uint8_t v_isExporting_1336_; 
v_isExporting_1336_ = lean_ctor_get_uint8(v_env_1334_, sizeof(void*)*13);
if (v_isExporting_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v_env_1334_);
lean_dec(v_declHint_1329_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_msg_1328_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
lean_inc_ref(v_env_1334_);
v___x_1338_ = l_Lean_Environment_setExporting(v_env_1334_, v___x_1335_);
lean_inc(v_declHint_1329_);
lean_inc_ref(v___x_1338_);
v___x_1339_ = l_Lean_Environment_contains(v___x_1338_, v_declHint_1329_, v_isExporting_1336_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_env_1334_);
lean_dec(v_declHint_1329_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_msg_1328_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_c_1348_; lean_object* v___x_1349_; 
v___x_1341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1342_ = lean_unsigned_to_nat(32u);
v___x_1343_ = lean_mk_empty_array_with_capacity(v___x_1342_);
lean_dec_ref(v___x_1343_);
v___x_1344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1345_ = l_Lean_Options_empty;
v___x_1346_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1338_);
lean_ctor_set(v___x_1346_, 1, v___x_1341_);
lean_ctor_set(v___x_1346_, 2, v___x_1344_);
lean_ctor_set(v___x_1346_, 3, v___x_1345_);
lean_inc(v_declHint_1329_);
v___x_1347_ = l_Lean_MessageData_ofConstName(v_declHint_1329_, v___x_1335_);
v_c_1348_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1348_, 0, v___x_1346_);
lean_ctor_set(v_c_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1334_, v_declHint_1329_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref(v_env_1334_);
lean_dec(v_declHint_1329_);
v___x_1350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v_c_1348_);
v___x_1352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_MessageData_note(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_msg_1328_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1391_; 
v_val_1357_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1359_ = v___x_1349_;
v_isShared_1360_ = v_isSharedCheck_1391_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_val_1357_);
lean_dec(v___x_1349_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1391_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_mod_1363_; uint8_t v___x_1364_; 
v___x_1361_ = l_Lean_Environment_header(v_env_1334_);
lean_dec_ref(v_env_1334_);
v___x_1362_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1361_);
v_mod_1363_ = lean_array_get(v___x_1332_, v___x_1362_, v_val_1357_);
lean_dec(v_val_1357_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l_Lean_isPrivateName(v_declHint_1329_);
lean_dec(v_declHint_1329_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_c_1348_);
v___x_1367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_MessageData_ofName(v_mod_1363_);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_MessageData_note(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_msg_1328_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1374_);
v___x_1376_ = v___x_1359_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1378_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v_c_1348_);
v___x_1380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_MessageData_ofName(v_mod_1363_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = l_Lean_MessageData_note(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_msg_1328_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1387_);
v___x_1389_ = v___x_1359_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1392_; 
lean_dec_ref(v_env_1334_);
lean_dec(v_declHint_1329_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_msg_1328_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg___boxed(lean_object* v_msg_1393_, lean_object* v_declHint_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1393_, v_declHint_1394_, v___y_1395_);
lean_dec(v___y_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(lean_object* v_msg_1398_, lean_object* v_declHint_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1417_; 
v___x_1407_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1398_, v_declHint_1399_, v___y_1405_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = l_Lean_unknownIdentifierMessageTag;
v___x_1413_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23___boxed(lean_object* v_msg_1418_, lean_object* v_declHint_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1418_, v_declHint_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(lean_object* v_ref_1428_, lean_object* v_msg_1429_, lean_object* v_declHint_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v_a_1439_; lean_object* v___x_1440_; 
v___x_1438_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1429_, v_declHint_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1428_, v_a_1439_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg___boxed(lean_object* v_ref_1441_, lean_object* v_msg_1442_, lean_object* v_declHint_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1441_, v_msg_1442_, v_declHint_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_ref_1441_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(lean_object* v_ref_1452_, lean_object* v_constName_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1461_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1462_ = 0;
lean_inc(v_constName_1453_);
v___x_1463_ = l_Lean_MessageData_ofConstName(v_constName_1453_, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1461_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1452_, v___x_1466_, v_constName_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_ref_1468_, lean_object* v_constName_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1468_, v_constName_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_ref_1468_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(lean_object* v_constName_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_ref_1486_; lean_object* v___x_1487_; 
v_ref_1486_ = lean_ctor_get(v___y_1483_, 2);
v___x_1487_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1486_, v_constName_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg___boxed(lean_object* v_constName_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(lean_object* v_constName_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; lean_object* v_env_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_st_ref_get(v___y_1503_);
v_env_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc_ref(v_env_1506_);
lean_dec(v___x_1505_);
v___x_1507_ = 0;
lean_inc(v_constName_1497_);
v___x_1508_ = l_Lean_Environment_find_x3f(v_env_1506_, v_constName_1497_, v___x_1507_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
return v___x_1509_;
}
else
{
lean_object* v_val_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_constName_1497_);
v_val_1510_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1508_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_val_1510_);
lean_dec(v___x_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 0);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_val_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2___boxed(lean_object* v_constName_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_constName_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1526_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(uint8_t v_suppressElabErrors_1533_, uint8_t v___y_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 1)
{
lean_object* v_pre_1536_; 
v_pre_1536_ = lean_ctor_get(v_x_1535_, 0);
switch(lean_obj_tag(v_pre_1536_))
{
case 1:
{
lean_object* v_pre_1537_; 
v_pre_1537_ = lean_ctor_get(v_pre_1536_, 0);
switch(lean_obj_tag(v_pre_1537_))
{
case 0:
{
lean_object* v_str_1538_; lean_object* v_str_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_str_1538_ = lean_ctor_get(v_x_1535_, 1);
v_str_1539_ = lean_ctor_get(v_pre_1536_, 1);
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8));
v___x_1541_ = lean_string_dec_eq(v_str_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2));
v___x_1543_ = lean_string_dec_eq(v_str_1539_, v___x_1542_);
if (v___x_1543_ == 0)
{
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___x_1545_ = lean_string_dec_eq(v_str_1538_, v___x_1544_);
if (v___x_1545_ == 0)
{
return v___x_1545_;
}
else
{
return v_suppressElabErrors_1533_;
}
}
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1));
v___x_1547_ = lean_string_dec_eq(v_str_1538_, v___x_1546_);
if (v___x_1547_ == 0)
{
return v___x_1547_;
}
else
{
return v_suppressElabErrors_1533_;
}
}
}
case 1:
{
lean_object* v_pre_1548_; 
v_pre_1548_ = lean_ctor_get(v_pre_1537_, 0);
if (lean_obj_tag(v_pre_1548_) == 0)
{
lean_object* v_str_1549_; lean_object* v_str_1550_; lean_object* v_str_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_str_1549_ = lean_ctor_get(v_x_1535_, 1);
v_str_1550_ = lean_ctor_get(v_pre_1536_, 1);
v_str_1551_ = lean_ctor_get(v_pre_1537_, 1);
v___x_1552_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2));
v___x_1553_ = lean_string_dec_eq(v_str_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3));
v___x_1555_ = lean_string_dec_eq(v_str_1550_, v___x_1554_);
if (v___x_1555_ == 0)
{
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4));
v___x_1557_ = lean_string_dec_eq(v_str_1549_, v___x_1556_);
if (v___x_1557_ == 0)
{
return v___x_1557_;
}
else
{
return v_suppressElabErrors_1533_;
}
}
}
}
else
{
return v___y_1534_;
}
}
default: 
{
return v___y_1534_;
}
}
}
case 0:
{
lean_object* v_str_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_str_1558_ = lean_ctor_get(v_x_1535_, 1);
v___x_1559_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5));
v___x_1560_ = lean_string_dec_eq(v_str_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
return v___x_1560_;
}
else
{
return v_suppressElabErrors_1533_;
}
}
default: 
{
return v___y_1534_;
}
}
}
else
{
return v___y_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1561_, lean_object* v___y_1562_, lean_object* v_x_1563_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1564_; uint8_t v___y_49471__boxed_1565_; uint8_t v_res_1566_; lean_object* v_r_1567_; 
v_suppressElabErrors_boxed_1564_ = lean_unbox(v_suppressElabErrors_1561_);
v___y_49471__boxed_1565_ = lean_unbox(v___y_1562_);
v_res_1566_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(v_suppressElabErrors_boxed_1564_, v___y_49471__boxed_1565_, v_x_1563_);
lean_dec(v_x_1563_);
v_r_1567_ = lean_box(v_res_1566_);
return v_r_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1568_, lean_object* v_msgData_1569_, uint8_t v_severity_1570_, uint8_t v_isSilent_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; uint8_t v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v_toCold_1585_; lean_object* v___y_1586_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; uint8_t v___y_1618_; uint8_t v___y_1619_; lean_object* v___y_1620_; uint8_t v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1642_; lean_object* v___y_1643_; uint8_t v___y_1644_; lean_object* v___y_1645_; uint8_t v___y_1646_; uint8_t v___y_1647_; lean_object* v___y_1648_; uint8_t v___y_1652_; uint8_t v___y_1653_; uint8_t v___y_1654_; uint8_t v___x_1665_; uint8_t v___y_1667_; uint8_t v___y_1668_; uint8_t v___y_1669_; uint8_t v___y_1671_; uint8_t v___x_1679_; 
v___x_1665_ = 2;
v___x_1679_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1570_, v___x_1665_);
if (v___x_1679_ == 0)
{
v___y_1671_ = v___x_1679_;
goto v___jp_1670_;
}
else
{
uint8_t v___x_1680_; 
lean_inc_ref(v_msgData_1569_);
v___x_1680_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1569_);
v___y_1671_ = v___x_1680_;
goto v___jp_1670_;
}
v___jp_1577_:
{
lean_object* v_currNamespace_1587_; lean_object* v_openDecls_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_env_1593_; lean_object* v_nextMacroScope_1594_; lean_object* v_ngen_1595_; lean_object* v_auxDeclNGen_1596_; lean_object* v_traceState_1597_; lean_object* v_cache_1598_; lean_object* v_recordedDeps_1599_; lean_object* v_messages_1600_; lean_object* v_infoState_1601_; lean_object* v_snapshotTasks_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1613_; 
v_currNamespace_1587_ = lean_ctor_get(v_toCold_1585_, 4);
v_openDecls_1588_ = lean_ctor_get(v_toCold_1585_, 5);
lean_inc(v_openDecls_1588_);
lean_inc(v_currNamespace_1587_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_currNamespace_1587_);
lean_ctor_set(v___x_1589_, 1, v_openDecls_1588_);
v___x_1590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___y_1578_);
lean_inc_ref(v___y_1581_);
lean_inc_ref(v___y_1584_);
v___x_1591_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1591_, 0, v___y_1584_);
lean_ctor_set(v___x_1591_, 1, v___y_1579_);
lean_ctor_set(v___x_1591_, 2, v___y_1583_);
lean_ctor_set(v___x_1591_, 3, v___y_1581_);
lean_ctor_set(v___x_1591_, 4, v___x_1590_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*5, v___y_1582_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*5 + 1, v___y_1580_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*5 + 2, v_isSilent_1571_);
v___x_1592_ = lean_st_ref_take(v___y_1586_);
v_env_1593_ = lean_ctor_get(v___x_1592_, 0);
v_nextMacroScope_1594_ = lean_ctor_get(v___x_1592_, 1);
v_ngen_1595_ = lean_ctor_get(v___x_1592_, 2);
v_auxDeclNGen_1596_ = lean_ctor_get(v___x_1592_, 3);
v_traceState_1597_ = lean_ctor_get(v___x_1592_, 4);
v_cache_1598_ = lean_ctor_get(v___x_1592_, 5);
v_recordedDeps_1599_ = lean_ctor_get(v___x_1592_, 6);
v_messages_1600_ = lean_ctor_get(v___x_1592_, 7);
v_infoState_1601_ = lean_ctor_get(v___x_1592_, 8);
v_snapshotTasks_1602_ = lean_ctor_get(v___x_1592_, 9);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1604_ = v___x_1592_;
v_isShared_1605_ = v_isSharedCheck_1613_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snapshotTasks_1602_);
lean_inc(v_infoState_1601_);
lean_inc(v_messages_1600_);
lean_inc(v_recordedDeps_1599_);
lean_inc(v_cache_1598_);
lean_inc(v_traceState_1597_);
lean_inc(v_auxDeclNGen_1596_);
lean_inc(v_ngen_1595_);
lean_inc(v_nextMacroScope_1594_);
lean_inc(v_env_1593_);
lean_dec(v___x_1592_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1613_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = l_Lean_MessageLog_add(v___x_1591_, v_messages_1600_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 7, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_env_1593_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_nextMacroScope_1594_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_ngen_1595_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_auxDeclNGen_1596_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_traceState_1597_);
lean_ctor_set(v_reuseFailAlloc_1612_, 5, v_cache_1598_);
lean_ctor_set(v_reuseFailAlloc_1612_, 6, v_recordedDeps_1599_);
lean_ctor_set(v_reuseFailAlloc_1612_, 7, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1612_, 8, v_infoState_1601_);
lean_ctor_set(v_reuseFailAlloc_1612_, 9, v_snapshotTasks_1602_);
v___x_1609_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_st_ref_put(v___y_1586_, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1606_);
return v___x_1611_;
}
}
}
v___jp_1614_:
{
lean_object* v_fileName_1623_; lean_object* v_fileMap_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1640_; 
v_fileName_1623_ = lean_ctor_get(v___y_1620_, 0);
v_fileMap_1624_ = lean_ctor_get(v___y_1620_, 1);
v___x_1625_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1569_);
v___x_1626_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v___x_1625_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1640_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1640_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_inc_ref_n(v_fileMap_1624_, 2);
v___x_1631_ = l_Lean_FileMap_toPosition(v_fileMap_1624_, v___y_1617_);
lean_dec(v___y_1617_);
v___x_1632_ = l_Lean_FileMap_toPosition(v_fileMap_1624_, v___y_1622_);
lean_dec(v___y_1622_);
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___x_1634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
if (v___y_1621_ == 0)
{
lean_del_object(v___x_1629_);
lean_dec_ref(v___y_1615_);
v___y_1578_ = v_a_1627_;
v___y_1579_ = v___x_1631_;
v___y_1580_ = v___y_1618_;
v___y_1581_ = v___x_1634_;
v___y_1582_ = v___y_1619_;
v___y_1583_ = v___x_1633_;
v___y_1584_ = v_fileName_1623_;
v_toCold_1585_ = v___y_1616_;
v___y_1586_ = v___y_1575_;
goto v___jp_1577_;
}
else
{
uint8_t v___x_1635_; 
lean_inc(v_a_1627_);
v___x_1635_ = l_Lean_MessageData_hasTag(v___y_1615_, v_a_1627_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1633_, 1);
lean_dec_ref(v___x_1631_);
lean_dec(v_a_1627_);
v___x_1636_ = lean_box(0);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1636_);
v___x_1638_ = v___x_1629_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
else
{
lean_del_object(v___x_1629_);
v___y_1578_ = v_a_1627_;
v___y_1579_ = v___x_1631_;
v___y_1580_ = v___y_1618_;
v___y_1581_ = v___x_1634_;
v___y_1582_ = v___y_1619_;
v___y_1583_ = v___x_1633_;
v___y_1584_ = v_fileName_1623_;
v_toCold_1585_ = v___y_1616_;
v___y_1586_ = v___y_1575_;
goto v___jp_1577_;
}
}
}
}
v___jp_1641_:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Syntax_getTailPos_x3f(v___y_1645_, v___y_1647_);
lean_dec(v___y_1645_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_inc(v___y_1648_);
v___y_1615_ = v___y_1642_;
v___y_1616_ = v___y_1643_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1646_;
v___y_1619_ = v___y_1647_;
v___y_1620_ = v___y_1643_;
v___y_1621_ = v___y_1644_;
v___y_1622_ = v___y_1648_;
goto v___jp_1614_;
}
else
{
lean_object* v_val_1650_; 
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___y_1615_ = v___y_1642_;
v___y_1616_ = v___y_1643_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1646_;
v___y_1619_ = v___y_1647_;
v___y_1620_ = v___y_1643_;
v___y_1621_ = v___y_1644_;
v___y_1622_ = v_val_1650_;
goto v___jp_1614_;
}
}
v___jp_1651_:
{
lean_object* v_toCold_1655_; lean_object* v_ref_1656_; uint8_t v_suppressElabErrors_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v_ref_1661_; lean_object* v___x_1662_; 
v_toCold_1655_ = lean_ctor_get(v___y_1574_, 0);
v_ref_1656_ = lean_ctor_get(v___y_1574_, 2);
v_suppressElabErrors_1657_ = lean_ctor_get_uint8(v___y_1574_, sizeof(void*)*3 + 2);
v___x_1658_ = lean_box(v_suppressElabErrors_1657_);
v___x_1659_ = lean_box(v___y_1652_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1660_, 0, v___x_1658_);
lean_closure_set(v___f_1660_, 1, v___x_1659_);
v_ref_1661_ = l_Lean_replaceRef(v_ref_1568_, v_ref_1656_);
v___x_1662_ = l_Lean_Syntax_getPos_x3f(v_ref_1661_, v___y_1653_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
v___y_1642_ = v___f_1660_;
v___y_1643_ = v_toCold_1655_;
v___y_1644_ = v_suppressElabErrors_1657_;
v___y_1645_ = v_ref_1661_;
v___y_1646_ = v___y_1654_;
v___y_1647_ = v___y_1653_;
v___y_1648_ = v___x_1663_;
goto v___jp_1641_;
}
else
{
lean_object* v_val_1664_; 
v_val_1664_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v___x_1662_, 1);
v___y_1642_ = v___f_1660_;
v___y_1643_ = v_toCold_1655_;
v___y_1644_ = v_suppressElabErrors_1657_;
v___y_1645_ = v_ref_1661_;
v___y_1646_ = v___y_1654_;
v___y_1647_ = v___y_1653_;
v___y_1648_ = v_val_1664_;
goto v___jp_1641_;
}
}
v___jp_1666_:
{
if (v___y_1669_ == 0)
{
v___y_1652_ = v___y_1667_;
v___y_1653_ = v___y_1668_;
v___y_1654_ = v_severity_1570_;
goto v___jp_1651_;
}
else
{
v___y_1652_ = v___y_1667_;
v___y_1653_ = v___y_1668_;
v___y_1654_ = v___x_1665_;
goto v___jp_1651_;
}
}
v___jp_1670_:
{
if (v___y_1671_ == 0)
{
uint8_t v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = 1;
v___x_1673_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1570_, v___x_1672_);
if (v___x_1673_ == 0)
{
v___y_1667_ = v___y_1671_;
v___y_1668_ = v___y_1671_;
v___y_1669_ = v___x_1673_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1674_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1574_);
v___x_1675_ = l_Lean_warningAsError;
v___x_1676_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v___x_1674_, v___x_1675_);
lean_dec_ref(v___x_1674_);
v___y_1667_ = v___y_1671_;
v___y_1668_ = v___y_1671_;
v___y_1669_ = v___x_1676_;
goto v___jp_1666_;
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v_msgData_1569_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1681_, lean_object* v_msgData_1682_, lean_object* v_severity_1683_, lean_object* v_isSilent_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v_severity_boxed_1690_; uint8_t v_isSilent_boxed_1691_; lean_object* v_res_1692_; 
v_severity_boxed_1690_ = lean_unbox(v_severity_1683_);
v_isSilent_boxed_1691_ = lean_unbox(v_isSilent_1684_);
v_res_1692_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1681_, v_msgData_1682_, v_severity_boxed_1690_, v_isSilent_boxed_1691_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_ref_1681_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(lean_object* v_msgData_1693_, uint8_t v_severity_1694_, uint8_t v_isSilent_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_ref_1703_; lean_object* v___x_1704_; 
v_ref_1703_ = lean_ctor_get(v___y_1700_, 2);
v___x_1704_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1703_, v_msgData_1693_, v_severity_1694_, v_isSilent_1695_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1705_, lean_object* v_severity_1706_, lean_object* v_isSilent_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_severity_boxed_1715_; uint8_t v_isSilent_boxed_1716_; lean_object* v_res_1717_; 
v_severity_boxed_1715_ = lean_unbox(v_severity_1706_);
v_isSilent_boxed_1716_ = lean_unbox(v_isSilent_1707_);
v_res_1717_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1705_, v_severity_boxed_1715_, v_isSilent_boxed_1716_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(lean_object* v_msgData_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = 2;
v___x_1727_ = 0;
v___x_1728_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1718_, v___x_1726_, v___x_1727_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1___boxed(lean_object* v_msgData_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v_msgData_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(lean_object* v_ref_1738_, lean_object* v_msgData_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = 2;
v___x_1748_ = 0;
v___x_1749_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1738_, v_msgData_1739_, v___x_1747_, v___x_1748_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0___boxed(lean_object* v_ref_1750_, lean_object* v_msgData_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1750_, v_msgData_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v_ref_1750_);
return v_res_1759_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(lean_object* v_ex_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
if (lean_obj_tag(v_ex_1763_) == 0)
{
lean_object* v_ref_1771_; lean_object* v_msg_1772_; lean_object* v___x_1773_; 
v_ref_1771_ = lean_ctor_get(v_ex_1763_, 0);
lean_inc(v_ref_1771_);
v_msg_1772_ = lean_ctor_get(v_ex_1763_, 1);
lean_inc_ref(v_msg_1772_);
lean_dec_ref_known(v_ex_1763_, 2);
v___x_1773_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1771_, v_msg_1772_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v_ref_1771_);
return v___x_1773_;
}
else
{
lean_object* v_id_1774_; uint8_t v___y_1776_; uint8_t v___x_1798_; 
v_id_1774_ = lean_ctor_get(v_ex_1763_, 0);
lean_inc(v_id_1774_);
v___x_1798_ = l_Lean_Elab_isAbortExceptionId(v_id_1774_);
if (v___x_1798_ == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = l_Lean_Exception_isInterrupt(v_ex_1763_);
lean_dec_ref_known(v_ex_1763_, 2);
v___y_1776_ = v___x_1799_;
goto v___jp_1775_;
}
else
{
lean_dec_ref_known(v_ex_1763_, 2);
v___y_1776_ = v___x_1798_;
goto v___jp_1775_;
}
v___jp_1775_:
{
if (v___y_1776_ == 0)
{
lean_object* v_ref_1777_; lean_object* v___x_1778_; 
v_ref_1777_ = lean_ctor_get(v___y_1768_, 2);
v___x_1778_ = l_Lean_InternalExceptionId_getName(v_id_1774_);
lean_dec(v_id_1774_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1);
v___x_1781_ = l_Lean_MessageData_ofName(v_a_1779_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v___x_1782_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1783_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1795_; 
v_a_1784_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1786_ = v___x_1778_;
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1778_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1788_ = lean_io_error_to_string(v_a_1784_);
v___x_1789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
v___x_1790_ = l_Lean_MessageData_ofFormat(v___x_1789_);
lean_inc(v_ref_1777_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_ref_1777_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1791_);
v___x_1793_ = v___x_1786_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v_id_1774_);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___boxed(lean_object* v_ex_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v_ex_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(lean_object* v_t_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v_infoState_1813_; uint8_t v_enabled_1814_; 
v___x_1812_ = lean_st_ref_get(v___y_1810_);
v_infoState_1813_ = lean_ctor_get(v___x_1812_, 8);
lean_inc_ref(v_infoState_1813_);
lean_dec(v___x_1812_);
v_enabled_1814_ = lean_ctor_get_uint8(v_infoState_1813_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1813_);
if (v_enabled_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v_t_1809_);
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; lean_object* v_infoState_1818_; lean_object* v_env_1819_; lean_object* v_nextMacroScope_1820_; lean_object* v_ngen_1821_; lean_object* v_auxDeclNGen_1822_; lean_object* v_traceState_1823_; lean_object* v_cache_1824_; lean_object* v_recordedDeps_1825_; lean_object* v_messages_1826_; lean_object* v_snapshotTasks_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1849_; 
v___x_1817_ = lean_st_ref_take(v___y_1810_);
v_infoState_1818_ = lean_ctor_get(v___x_1817_, 8);
v_env_1819_ = lean_ctor_get(v___x_1817_, 0);
v_nextMacroScope_1820_ = lean_ctor_get(v___x_1817_, 1);
v_ngen_1821_ = lean_ctor_get(v___x_1817_, 2);
v_auxDeclNGen_1822_ = lean_ctor_get(v___x_1817_, 3);
v_traceState_1823_ = lean_ctor_get(v___x_1817_, 4);
v_cache_1824_ = lean_ctor_get(v___x_1817_, 5);
v_recordedDeps_1825_ = lean_ctor_get(v___x_1817_, 6);
v_messages_1826_ = lean_ctor_get(v___x_1817_, 7);
v_snapshotTasks_1827_ = lean_ctor_get(v___x_1817_, 9);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1829_ = v___x_1817_;
v_isShared_1830_ = v_isSharedCheck_1849_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snapshotTasks_1827_);
lean_inc(v_infoState_1818_);
lean_inc(v_messages_1826_);
lean_inc(v_recordedDeps_1825_);
lean_inc(v_cache_1824_);
lean_inc(v_traceState_1823_);
lean_inc(v_auxDeclNGen_1822_);
lean_inc(v_ngen_1821_);
lean_inc(v_nextMacroScope_1820_);
lean_inc(v_env_1819_);
lean_dec(v___x_1817_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1849_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
uint8_t v_enabled_1831_; lean_object* v_assignment_1832_; lean_object* v_lazyAssignment_1833_; lean_object* v_trees_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1848_; 
v_enabled_1831_ = lean_ctor_get_uint8(v_infoState_1818_, sizeof(void*)*3);
v_assignment_1832_ = lean_ctor_get(v_infoState_1818_, 0);
v_lazyAssignment_1833_ = lean_ctor_get(v_infoState_1818_, 1);
v_trees_1834_ = lean_ctor_get(v_infoState_1818_, 2);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_infoState_1818_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1836_ = v_infoState_1818_;
v_isShared_1837_ = v_isSharedCheck_1848_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_trees_1834_);
lean_inc(v_lazyAssignment_1833_);
lean_inc(v_assignment_1832_);
lean_dec(v_infoState_1818_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1848_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = l_Lean_PersistentArray_push___redArg(v_trees_1834_, v_t_1809_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 2, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_assignment_1832_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_lazyAssignment_1833_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v___x_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1847_, sizeof(void*)*3, v_enabled_1831_);
v___x_1841_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 8, v___x_1841_);
v___x_1843_ = v___x_1829_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_env_1819_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_nextMacroScope_1820_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_ngen_1821_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_auxDeclNGen_1822_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_traceState_1823_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_cache_1824_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_recordedDeps_1825_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_messages_1826_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1846_, 9, v_snapshotTasks_1827_);
v___x_1843_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_st_ref_put(v___y_1810_, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1838_);
return v___x_1845_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_t_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_1850_, v___y_1851_);
lean_dec(v___y_1851_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_unsigned_to_nat(32u);
v___x_1855_ = lean_mk_empty_array_with_capacity(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1857_ = ((size_t)5ULL);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_unsigned_to_nat(32u);
v___x_1860_ = lean_mk_empty_array_with_capacity(v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0);
v___x_1862_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
lean_ctor_set(v___x_1862_, 2, v___x_1858_);
lean_ctor_set(v___x_1862_, 3, v___x_1858_);
lean_ctor_set_usize(v___x_1862_, 4, v___x_1857_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(lean_object* v_t_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v_infoState_1872_; uint8_t v_enabled_1873_; 
v___x_1871_ = lean_st_ref_get(v___y_1869_);
v_infoState_1872_ = lean_ctor_get(v___x_1871_, 8);
lean_inc_ref(v_infoState_1872_);
lean_dec(v___x_1871_);
v_enabled_1873_ = lean_ctor_get_uint8(v_infoState_1872_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1872_);
if (v_enabled_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v_t_1863_);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
v___x_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_t_1863_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v___x_1877_, v___y_1869_);
return v___x_1878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___boxed(lean_object* v_t_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v_t_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(lean_object* v_info_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_info_1888_);
v___x_1897_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v___x_1896_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1___boxed(lean_object* v_info_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v_info_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13));
v___x_1946_ = l_String_toRawSubstring_x27(v___x_1945_);
return v___x_1946_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9));
v___x_1970_ = l_String_toRawSubstring_x27(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(uint8_t v___x_1985_, lean_object* v_option_1986_, lean_object* v_fst_1987_, uint8_t v___x_1988_, lean_object* v_fst_1989_, lean_object* v_fst_1990_, lean_object* v_snd_1991_, lean_object* v_mkStructInst_1992_, lean_object* v_seenFields_1993_, lean_object* v_fields_1994_, lean_object* v_value_1995_, lean_object* v_____r_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___y_2005_; lean_object* v_source_x3f_2006_; lean_object* v_seenFields_2007_; lean_object* v_fields_2008_; lean_object* v___y_2009_; lean_object* v_value_2033_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8));
lean_inc(v_value_1995_);
v___x_2047_ = l_Lean_Syntax_isOfKind(v_value_1995_, v___x_2046_);
if (v___x_2047_ == 0)
{
v_value_2033_ = v_value_1995_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(1u);
v___x_2049_ = l_Lean_Syntax_getArg(v_value_1995_, v___x_2048_);
if (v___x_1985_ == 0)
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10));
lean_inc(v___x_2049_);
v___x_2080_ = l_Lean_Syntax_isOfKind(v___x_2049_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v___x_2049_);
v_value_2033_ = v_value_1995_;
goto v___jp_2032_;
}
else
{
goto v___jp_2050_;
}
}
else
{
goto v___jp_2050_;
}
v___jp_2050_:
{
lean_object* v_toCold_2051_; lean_object* v_ref_2052_; lean_object* v_quotContext_2053_; lean_object* v_currMacroScope_2054_; lean_object* v_ref_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_toCold_2051_ = lean_ctor_get(v___y_2001_, 0);
v_ref_2052_ = lean_ctor_get(v___y_2001_, 2);
v_quotContext_2053_ = lean_ctor_get(v_toCold_2051_, 8);
v_currMacroScope_2054_ = lean_ctor_get(v_toCold_2051_, 9);
v_ref_2055_ = l_Lean_replaceRef(v_value_1995_, v_ref_2052_);
lean_dec(v_value_1995_);
v___x_2056_ = l_Lean_SourceInfo_fromRef(v_ref_2055_, v___x_1985_);
lean_dec(v_ref_2055_);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_2058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14);
v___x_2059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17));
lean_inc_n(v_currMacroScope_2054_, 2);
lean_inc_n(v_quotContext_2053_, 2);
v___x_2060_ = l_Lean_addMacroScope(v_quotContext_2053_, v___x_2059_, v_currMacroScope_2054_);
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20));
lean_inc_n(v___x_2056_, 7);
v___x_2062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2056_);
lean_ctor_set(v___x_2062_, 1, v___x_2058_);
lean_ctor_set(v___x_2062_, 2, v___x_2060_);
lean_ctor_set(v___x_2062_, 3, v___x_2061_);
v___x_2063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22));
v___x_2065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23));
v___x_2066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2056_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24);
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25));
v___x_2069_ = l_Lean_addMacroScope(v_quotContext_2053_, v___x_2068_, v_currMacroScope_2054_);
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29));
v___x_2071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2056_);
lean_ctor_set(v___x_2071_, 1, v___x_2067_);
lean_ctor_set(v___x_2071_, 2, v___x_2069_);
lean_ctor_set(v___x_2071_, 3, v___x_2070_);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30));
v___x_2073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2056_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_2075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2056_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Lean_Syntax_node5(v___x_2056_, v___x_2064_, v___x_2066_, v___x_2071_, v___x_2073_, v___x_2049_, v___x_2075_);
v___x_2077_ = l_Lean_Syntax_node1(v___x_2056_, v___x_2063_, v___x_2076_);
v___x_2078_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2057_, v___x_2062_, v___x_2077_);
v_value_2033_ = v___x_2078_;
goto v___jp_2032_;
}
}
v___jp_2004_:
{
lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_ref_2010_ = lean_ctor_get(v___y_2009_, 2);
v___x_2011_ = l_Lean_SourceInfo_fromRef(v_ref_2010_, v___x_1985_);
v___x_2012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1));
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3));
lean_inc(v_fst_1987_);
v___x_2014_ = l_Lean_mkCIdentFrom(v_option_1986_, v_fst_1987_, v___x_1988_);
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2011_, 5);
v___x_2017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
lean_ctor_set(v___x_2017_, 1, v___x_2015_);
lean_ctor_set(v___x_2017_, 2, v___x_2016_);
lean_inc_ref_n(v___x_2017_, 3);
v___x_2018_ = l_Lean_Syntax_node2(v___x_2011_, v___x_2013_, v___x_2014_, v___x_2017_);
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5));
v___x_2020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_2021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2011_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = l_Lean_Syntax_node3(v___x_2011_, v___x_2019_, v___x_2021_, v___x_2017_, v___y_2005_);
v___x_2023_ = l_Lean_Syntax_node3(v___x_2011_, v___x_2015_, v___x_2017_, v___x_2017_, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_node2(v___x_2011_, v___x_2012_, v___x_2018_, v___x_2023_);
v___x_2025_ = lean_array_push(v_fields_2008_, v___x_2024_);
v___x_2026_ = l_Lean_NameSet_insert(v_seenFields_2007_, v_fst_1987_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2025_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_source_x3f_2006_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
v___jp_2032_:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_NameSet_contains(v_fst_1989_, v_fst_1987_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_fields_1994_);
lean_dec(v_seenFields_1993_);
lean_dec_ref(v_mkStructInst_1992_);
v___y_2005_ = v_value_2033_;
v_source_x3f_2006_ = v_fst_1990_;
v_seenFields_2007_ = v_fst_1989_;
v_fields_2008_ = v_snd_1991_;
v___y_2009_ = v___y_2001_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2035_; 
lean_dec(v_fst_1989_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
v___x_2035_ = lean_apply_9(v_mkStructInst_1992_, v_fst_1990_, v_snd_1991_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, lean_box(0));
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_a_2036_);
v___y_2005_ = v_value_2033_;
v_source_x3f_2006_ = v___x_2037_;
v_seenFields_2007_ = v_seenFields_1993_;
v_fields_2008_ = v_fields_1994_;
v___y_2009_ = v___y_2001_;
goto v___jp_2004_;
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_value_2033_);
lean_dec_ref(v_fields_1994_);
lean_dec(v_seenFields_1993_);
lean_dec(v_fst_1987_);
v_a_2038_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2035_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2035_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v___x_2081_ = _args[0];
lean_object* v_option_2082_ = _args[1];
lean_object* v_fst_2083_ = _args[2];
lean_object* v___x_2084_ = _args[3];
lean_object* v_fst_2085_ = _args[4];
lean_object* v_fst_2086_ = _args[5];
lean_object* v_snd_2087_ = _args[6];
lean_object* v_mkStructInst_2088_ = _args[7];
lean_object* v_seenFields_2089_ = _args[8];
lean_object* v_fields_2090_ = _args[9];
lean_object* v_value_2091_ = _args[10];
lean_object* v_____r_2092_ = _args[11];
lean_object* v___y_2093_ = _args[12];
lean_object* v___y_2094_ = _args[13];
lean_object* v___y_2095_ = _args[14];
lean_object* v___y_2096_ = _args[15];
lean_object* v___y_2097_ = _args[16];
lean_object* v___y_2098_ = _args[17];
lean_object* v___y_2099_ = _args[18];
_start:
{
uint8_t v___x_50206__boxed_2100_; uint8_t v___x_50208__boxed_2101_; lean_object* v_res_2102_; 
v___x_50206__boxed_2100_ = lean_unbox(v___x_2081_);
v___x_50208__boxed_2101_ = lean_unbox(v___x_2084_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_50206__boxed_2100_, v_option_2082_, v_fst_2083_, v___x_50208__boxed_2101_, v_fst_2085_, v_fst_2086_, v_snd_2087_, v_mkStructInst_2088_, v_seenFields_2089_, v_fields_2090_, v_value_2091_, v_____r_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v_option_2082_);
return v_res_2102_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2107_ = lean_box(1);
v___x_2108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1);
v___x_2110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___x_2108_);
lean_ctor_set(v___x_2110_, 2, v___x_2107_);
return v___x_2110_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3));
v___x_2115_ = l_Lean_Expr_const___override(v___x_2114_, v___x_2113_);
return v___x_2115_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(lean_object* v_structName_2122_, uint8_t v_recover_2123_, lean_object* v_as_2124_, size_t v_sz_2125_, size_t v_i_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_fst_2136_; lean_object* v_fst_2137_; lean_object* v_snd_2138_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_usize_dec_lt(v_i_2126_, v_sz_2125_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_dec(v_structName_2122_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_b_2127_);
return v___x_2146_;
}
else
{
lean_object* v_snd_2147_; lean_object* v_fst_2148_; lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2256_; 
v_snd_2147_ = lean_ctor_get(v_b_2127_, 1);
lean_inc(v_snd_2147_);
v_fst_2148_ = lean_ctor_get(v_b_2127_, 0);
lean_inc(v_fst_2148_);
lean_dec_ref(v_b_2127_);
v_fst_2149_ = lean_ctor_get(v_snd_2147_, 0);
v_snd_2150_ = lean_ctor_get(v_snd_2147_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_snd_2147_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2152_ = v_snd_2147_;
v_isShared_2153_ = v_isSharedCheck_2256_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_snd_2150_);
lean_inc(v_fst_2149_);
lean_dec(v_snd_2147_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2256_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___y_2155_; uint8_t v___y_2156_; lean_object* v_a_2169_; lean_object* v___y_2173_; lean_object* v_a_2181_; lean_object* v_ref_2182_; lean_object* v_option_2183_; lean_object* v_value_2184_; uint8_t v_bool_2185_; lean_object* v_mkStructInst_2186_; lean_object* v_seenFields_2187_; lean_object* v_fields_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_a_2181_ = lean_array_uget_borrowed(v_as_2124_, v_i_2126_);
v_ref_2182_ = lean_ctor_get(v_a_2181_, 0);
v_option_2183_ = lean_ctor_get(v_a_2181_, 1);
v_value_2184_ = lean_ctor_get(v_a_2181_, 2);
v_bool_2185_ = lean_ctor_get_uint8(v_a_2181_, sizeof(void*)*3);
lean_inc(v_structName_2122_);
v_mkStructInst_2186_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed), 10, 1);
lean_closure_set(v_mkStructInst_2186_, 0, v_structName_2122_);
v_seenFields_2187_ = l_Lean_NameSet_empty;
v_fields_2188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v___x_2189_ = l_Lean_TSyntax_getId(v_option_2183_);
v___x_2190_ = l_Lean_Name_eraseMacroScopes(v___x_2189_);
lean_dec(v___x_2189_);
v___x_2191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7));
v___x_2192_ = lean_name_eq(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
lean_inc(v___x_2190_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2190_);
lean_inc(v_structName_2122_);
lean_inc(v_option_2183_);
v___x_2195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2195_, 0, v_option_2183_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
lean_ctor_set(v___x_2195_, 2, v___x_2193_);
lean_ctor_set(v___x_2195_, 3, v_structName_2122_);
v___x_2196_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v___x_2195_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_toCold_2197_; lean_object* v_currRecDepth_2198_; lean_object* v_ref_2199_; uint16_t v_optionFlags_2200_; uint8_t v_suppressElabErrors_2201_; uint8_t v_isRecordingDeps_2202_; lean_object* v_ref_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref_known(v___x_2196_, 1);
v_toCold_2197_ = lean_ctor_get(v___y_2132_, 0);
v_currRecDepth_2198_ = lean_ctor_get(v___y_2132_, 1);
v_ref_2199_ = lean_ctor_get(v___y_2132_, 2);
v_optionFlags_2200_ = lean_ctor_get_uint16(v___y_2132_, sizeof(void*)*3);
v_suppressElabErrors_2201_ = lean_ctor_get_uint8(v___y_2132_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2202_ = lean_ctor_get_uint8(v___y_2132_, sizeof(void*)*3 + 3);
v_ref_2203_ = l_Lean_replaceRef(v_option_2183_, v_ref_2199_);
lean_inc(v_currRecDepth_2198_);
lean_inc_ref(v_toCold_2197_);
v___x_2204_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2204_, 0, v_toCold_2197_);
lean_ctor_set(v___x_2204_, 1, v_currRecDepth_2198_);
lean_ctor_set(v___x_2204_, 2, v_ref_2203_);
lean_ctor_set_uint16(v___x_2204_, sizeof(void*)*3, v_optionFlags_2200_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*3 + 2, v_suppressElabErrors_2201_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*3 + 3, v_isRecordingDeps_2202_);
lean_inc(v___x_2190_);
lean_inc(v_structName_2122_);
v___x_2205_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_2122_, v___x_2190_, v___y_2130_, v___y_2131_, v___x_2204_, v___y_2133_);
lean_dec_ref_known(v___x_2204_, 3);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
if (v_bool_2185_ == 0)
{
lean_object* v_fst_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v___x_2190_);
lean_del_object(v___x_2152_);
v_fst_2207_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_fst_2207_);
lean_dec(v_a_2206_);
v___x_2208_ = lean_box(0);
lean_inc(v_value_2184_);
lean_inc(v_snd_2150_);
lean_inc(v_fst_2148_);
lean_inc(v_fst_2149_);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2192_, v_option_2183_, v_fst_2207_, v___x_2145_, v_fst_2149_, v_fst_2148_, v_snd_2150_, v_mkStructInst_2186_, v_seenFields_2187_, v_fields_2188_, v_value_2184_, v___x_2208_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
v___y_2173_ = v___x_2209_;
goto v___jp_2172_;
}
else
{
lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2237_; 
v_fst_2210_ = lean_ctor_get(v_a_2206_, 0);
v_snd_2211_ = lean_ctor_get(v_a_2206_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2213_ = v_a_2206_;
v_isShared_2214_ = v_isSharedCheck_2237_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snd_2211_);
lean_inc(v_fst_2210_);
lean_dec(v_a_2206_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2237_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_snd_2211_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = l_Lean_ConstantInfo_type(v_a_2216_);
lean_dec(v_a_2216_);
v___x_2218_ = l_Lean_Expr_bindingBody_x21(v___x_2217_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4);
v___x_2220_ = lean_expr_eqv(v___x_2218_, v___x_2219_);
lean_dec_ref(v___x_2218_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6);
v___x_2222_ = l_Lean_MessageData_ofName(v___x_2190_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 7);
lean_ctor_set(v___x_2213_, 1, v___x_2222_);
lean_ctor_set(v___x_2213_, 0, v___x_2221_);
v___x_2224_ = v___x_2213_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8);
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 7);
lean_ctor_set(v___x_2152_, 1, v___x_2225_);
lean_ctor_set(v___x_2152_, 0, v___x_2224_);
v___x_2227_ = v___x_2152_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_2182_, v___x_2227_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
lean_inc(v_value_2184_);
lean_inc(v_snd_2150_);
lean_inc(v_fst_2148_);
lean_inc(v_fst_2149_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2192_, v_option_2183_, v_fst_2210_, v___x_2145_, v_fst_2149_, v_fst_2148_, v_snd_2150_, v_mkStructInst_2186_, v_seenFields_2187_, v_fields_2188_, v_value_2184_, v_a_2229_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
v___y_2173_ = v___x_2230_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2231_; 
lean_dec(v_fst_2210_);
lean_dec_ref(v_mkStructInst_2186_);
v_a_2231_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2228_, 1);
v_a_2169_ = v_a_2231_;
goto v___jp_2168_;
}
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_del_object(v___x_2213_);
lean_dec(v___x_2190_);
lean_del_object(v___x_2152_);
v___x_2234_ = lean_box(0);
lean_inc(v_value_2184_);
lean_inc(v_snd_2150_);
lean_inc(v_fst_2148_);
lean_inc(v_fst_2149_);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2192_, v_option_2183_, v_fst_2210_, v___x_2145_, v_fst_2149_, v_fst_2148_, v_snd_2150_, v_mkStructInst_2186_, v_seenFields_2187_, v_fields_2188_, v_value_2184_, v___x_2234_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
v___y_2173_ = v___x_2235_;
goto v___jp_2172_;
}
}
else
{
lean_object* v_a_2236_; 
lean_del_object(v___x_2213_);
lean_dec(v_fst_2210_);
lean_dec(v___x_2190_);
lean_dec_ref(v_mkStructInst_2186_);
lean_del_object(v___x_2152_);
v_a_2236_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2215_, 1);
v_a_2169_ = v_a_2236_;
goto v___jp_2168_;
}
}
}
}
else
{
lean_object* v_a_2238_; 
lean_dec(v___x_2190_);
lean_dec_ref(v_mkStructInst_2186_);
lean_del_object(v___x_2152_);
v_a_2238_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2205_, 1);
v_a_2169_ = v_a_2238_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2239_; 
lean_dec(v___x_2190_);
lean_dec_ref(v_mkStructInst_2186_);
lean_del_object(v___x_2152_);
v_a_2239_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2196_, 1);
v_a_2169_ = v_a_2239_;
goto v___jp_2168_;
}
}
else
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
lean_dec(v___x_2190_);
lean_dec_ref(v_mkStructInst_2186_);
lean_del_object(v___x_2152_);
v___x_2240_ = lean_array_get_size(v_snd_2150_);
v___x_2241_ = lean_nat_dec_eq(v___x_2240_, v___x_2144_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_inc(v_fst_2148_);
lean_inc(v_structName_2122_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_2122_, v_fst_2148_, v_snd_2150_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2252_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 1);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_box(0);
lean_inc(v_structName_2122_);
lean_inc(v_a_2181_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2181_, v_structName_2122_, v___x_2249_, v___x_2248_, v_seenFields_2187_, v_fields_2188_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
v___y_2173_ = v___x_2250_;
goto v___jp_2172_;
}
}
}
else
{
lean_object* v_a_2253_; 
v_a_2253_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2242_, 1);
v_a_2169_ = v_a_2253_;
goto v___jp_2168_;
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_box(0);
lean_inc(v_snd_2150_);
lean_inc(v_fst_2149_);
lean_inc(v_fst_2148_);
lean_inc(v_structName_2122_);
lean_inc(v_a_2181_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2181_, v_structName_2122_, v___x_2254_, v_fst_2148_, v_fst_2149_, v_snd_2150_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
v___y_2173_ = v___x_2255_;
goto v___jp_2172_;
}
}
v___jp_2154_:
{
if (v___y_2156_ == 0)
{
if (v_recover_2123_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_structName_2122_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___y_2155_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v___y_2155_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_dec_ref_known(v___x_2158_, 1);
v_fst_2136_ = v_fst_2148_;
v_fst_2137_ = v_fst_2149_;
v_snd_2138_ = v_snd_2150_;
goto v___jp_2135_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_structName_2122_);
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
else
{
lean_object* v___x_2167_; 
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_structName_2122_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___y_2155_);
return v___x_2167_;
}
}
v___jp_2168_:
{
uint8_t v___x_2170_; 
v___x_2170_ = l_Lean_Exception_isInterrupt(v_a_2169_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; 
lean_inc_ref(v_a_2169_);
v___x_2171_ = l_Lean_Exception_isRuntime(v_a_2169_);
v___y_2155_ = v_a_2169_;
v___y_2156_ = v___x_2171_;
goto v___jp_2154_;
}
else
{
v___y_2155_ = v_a_2169_;
v___y_2156_ = v___x_2170_;
goto v___jp_2154_;
}
}
v___jp_2172_:
{
if (lean_obj_tag(v___y_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v_snd_2175_; lean_object* v_snd_2176_; lean_object* v_fst_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; 
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2148_);
v_a_2174_ = lean_ctor_get(v___y_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___y_2173_, 1);
v_snd_2175_ = lean_ctor_get(v_a_2174_, 1);
lean_inc(v_snd_2175_);
lean_dec(v_a_2174_);
v_snd_2176_ = lean_ctor_get(v_snd_2175_, 1);
lean_inc(v_snd_2176_);
v_fst_2177_ = lean_ctor_get(v_snd_2175_, 0);
lean_inc(v_fst_2177_);
lean_dec(v_snd_2175_);
v_fst_2178_ = lean_ctor_get(v_snd_2176_, 0);
lean_inc(v_fst_2178_);
v_snd_2179_ = lean_ctor_get(v_snd_2176_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_snd_2176_);
v_fst_2136_ = v_fst_2177_;
v_fst_2137_ = v_fst_2178_;
v_snd_2138_ = v_snd_2179_;
goto v___jp_2135_;
}
else
{
lean_object* v_a_2180_; 
v_a_2180_ = lean_ctor_get(v___y_2173_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___y_2173_, 1);
v_a_2169_ = v_a_2180_;
goto v___jp_2168_;
}
}
}
}
v___jp_2135_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; 
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_fst_2137_);
lean_ctor_set(v___x_2139_, 1, v_snd_2138_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_fst_2136_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = ((size_t)1ULL);
v___x_2142_ = lean_usize_add(v_i_2126_, v___x_2141_);
v_i_2126_ = v___x_2142_;
v_b_2127_ = v___x_2140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___boxed(lean_object* v_structName_2257_, lean_object* v_recover_2258_, lean_object* v_as_2259_, lean_object* v_sz_2260_, lean_object* v_i_2261_, lean_object* v_b_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
uint8_t v_recover_boxed_2270_; size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_recover_boxed_2270_ = lean_unbox(v_recover_2258_);
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2260_);
lean_dec(v_sz_2260_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2257_, v_recover_boxed_2270_, v_as_2259_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_as_2259_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0(lean_object* v_structName_2274_, uint8_t v_recover_2275_, lean_object* v_items_2276_, size_t v_sz_2277_, size_t v___x_2278_, lean_object* v___x_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_a_2288_; lean_object* v___x_2301_; 
lean_inc(v_structName_2274_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2274_, v_recover_2275_, v_items_2276_, v_sz_2277_, v___x_2278_, v___x_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v_snd_2303_; lean_object* v_fst_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2381_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v_snd_2303_ = lean_ctor_get(v_a_2302_, 1);
v_fst_2304_ = lean_ctor_get(v_a_2302_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_a_2302_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2306_ = v_a_2302_;
v_isShared_2307_ = v_isSharedCheck_2381_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2303_);
lean_inc(v_fst_2304_);
lean_dec(v_a_2302_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2381_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
if (lean_obj_tag(v_fst_2304_) == 0)
{
lean_object* v_snd_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2340_; 
v_snd_2308_ = lean_ctor_get(v_snd_2303_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_snd_2303_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v_snd_2303_, 0);
lean_dec(v_unused_2341_);
v___x_2310_ = v_snd_2303_;
v_isShared_2311_ = v_isSharedCheck_2340_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_snd_2308_);
lean_dec(v_snd_2303_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2340_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_ref_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v_ref_2312_ = lean_ctor_get(v___y_2284_, 2);
v___x_2313_ = 0;
v___x_2314_ = l_Lean_SourceInfo_fromRef(v_ref_2312_, v___x_2313_);
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2314_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 2);
lean_ctor_set(v___x_2310_, 1, v___x_2316_);
lean_ctor_set(v___x_2310_, 0, v___x_2314_);
v___x_2318_ = v___x_2310_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2314_, 5);
v___x_2321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2314_);
lean_ctor_set(v___x_2321_, 1, v___x_2319_);
lean_ctor_set(v___x_2321_, 2, v___x_2320_);
v___x_2322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2324_ = l_Lean_Syntax_SepArray_ofElems(v___x_2323_, v_snd_2308_);
lean_dec(v_snd_2308_);
v___x_2325_ = l_Array_append___redArg(v___x_2320_, v___x_2324_);
lean_dec_ref(v___x_2324_);
v___x_2326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2314_);
lean_ctor_set(v___x_2326_, 1, v___x_2319_);
lean_ctor_set(v___x_2326_, 2, v___x_2325_);
v___x_2327_ = l_Lean_Syntax_node1(v___x_2314_, v___x_2322_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_2321_);
v___x_2329_ = l_Lean_Syntax_node1(v___x_2314_, v___x_2328_, v___x_2321_);
v___x_2330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 2);
lean_ctor_set(v___x_2306_, 1, v___x_2330_);
lean_ctor_set(v___x_2306_, 0, v___x_2314_);
v___x_2332_ = v___x_2306_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc(v_structName_2274_);
v___x_2333_ = l_Lean_mkCIdent(v_structName_2274_);
lean_inc_n(v___x_2314_, 2);
v___x_2334_ = l_Lean_Syntax_node2(v___x_2314_, v___x_2319_, v___x_2332_, v___x_2333_);
v___x_2335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2314_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_Syntax_node6(v___x_2314_, v___x_2315_, v___x_2318_, v___x_2321_, v___x_2327_, v___x_2329_, v___x_2334_, v___x_2336_);
v_a_2288_ = v___x_2337_;
goto v___jp_2287_;
}
}
}
}
else
{
lean_object* v_snd_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2379_; 
v_snd_2342_ = lean_ctor_get(v_snd_2303_, 1);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_snd_2303_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; 
v_unused_2380_ = lean_ctor_get(v_snd_2303_, 0);
lean_dec(v_unused_2380_);
v___x_2344_ = v_snd_2303_;
v_isShared_2345_ = v_isSharedCheck_2379_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_snd_2342_);
lean_dec(v_snd_2303_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2379_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_val_2346_; lean_object* v_ref_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v_val_2346_ = lean_ctor_get(v_fst_2304_, 0);
lean_inc(v_val_2346_);
lean_dec_ref_known(v_fst_2304_, 1);
v_ref_2347_ = lean_ctor_get(v___y_2284_, 2);
v___x_2348_ = 0;
v___x_2349_ = l_Lean_SourceInfo_fromRef(v_ref_2347_, v___x_2348_);
v___x_2350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2349_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 2);
lean_ctor_set(v___x_2344_, 1, v___x_2351_);
lean_ctor_set(v___x_2344_, 0, v___x_2349_);
v___x_2353_ = v___x_2344_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
lean_inc_n(v___x_2349_, 2);
v___x_2355_ = l_Lean_Syntax_node1(v___x_2349_, v___x_2354_, v_val_2346_);
v___x_2356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 2);
lean_ctor_set(v___x_2306_, 1, v___x_2356_);
lean_ctor_set(v___x_2306_, 0, v___x_2349_);
v___x_2358_ = v___x_2306_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_inc_n(v___x_2349_, 8);
v___x_2359_ = l_Lean_Syntax_node2(v___x_2349_, v___x_2354_, v___x_2355_, v___x_2358_);
v___x_2360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_2362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2363_ = l_Lean_Syntax_SepArray_ofElems(v___x_2362_, v_snd_2342_);
lean_dec(v_snd_2342_);
v___x_2364_ = l_Array_append___redArg(v___x_2361_, v___x_2363_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2349_);
lean_ctor_set(v___x_2365_, 1, v___x_2354_);
lean_ctor_set(v___x_2365_, 2, v___x_2364_);
v___x_2366_ = l_Lean_Syntax_node1(v___x_2349_, v___x_2360_, v___x_2365_);
v___x_2367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_2368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2349_);
lean_ctor_set(v___x_2368_, 1, v___x_2354_);
lean_ctor_set(v___x_2368_, 2, v___x_2361_);
v___x_2369_ = l_Lean_Syntax_node1(v___x_2349_, v___x_2367_, v___x_2368_);
v___x_2370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_2371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2349_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
lean_inc(v_structName_2274_);
v___x_2372_ = l_Lean_mkCIdent(v_structName_2274_);
v___x_2373_ = l_Lean_Syntax_node2(v___x_2349_, v___x_2354_, v___x_2371_, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2349_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_Syntax_node6(v___x_2349_, v___x_2350_, v___x_2353_, v___x_2359_, v___x_2366_, v___x_2369_, v___x_2373_, v___x_2375_);
v_a_2288_ = v___x_2376_;
goto v___jp_2287_;
}
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_structName_2274_);
v_a_2382_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2301_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2301_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
v___jp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Lean_mkConst(v_structName_2274_, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
v___x_2292_ = 1;
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_box(v___x_2292_);
v___x_2295_ = lean_box(v___x_2292_);
v___x_2296_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2296_, 0, v_a_2288_);
lean_closure_set(v___x_2296_, 1, v___x_2291_);
lean_closure_set(v___x_2296_, 2, v___x_2294_);
lean_closure_set(v___x_2296_, 3, v___x_2295_);
lean_closure_set(v___x_2296_, 4, v___x_2293_);
v___x_2297_ = 1;
v___x_2298_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2296_, v___x_2297_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_a_2299_, v___y_2283_);
return v___x_2300_;
}
else
{
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0___boxed(lean_object* v_structName_2390_, lean_object* v_recover_2391_, lean_object* v_items_2392_, lean_object* v_sz_2393_, lean_object* v___x_2394_, lean_object* v___x_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
uint8_t v_recover_boxed_2403_; size_t v_sz_boxed_2404_; size_t v___x_50791__boxed_2405_; lean_object* v_res_2406_; 
v_recover_boxed_2403_ = lean_unbox(v_recover_2391_);
v_sz_boxed_2404_ = lean_unbox_usize(v_sz_2393_);
lean_dec(v_sz_2393_);
v___x_50791__boxed_2405_ = lean_unbox_usize(v___x_2394_);
lean_dec(v___x_2394_);
v_res_2406_ = l_Lean_Elab_Tactic_elabConfig___lam__0(v_structName_2390_, v_recover_boxed_2403_, v_items_2392_, v_sz_boxed_2404_, v___x_50791__boxed_2405_, v___x_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v_items_2392_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v_env_2412_; lean_object* v___x_2413_; lean_object* v_toCold_2414_; lean_object* v_mctx_2415_; lean_object* v_currNamespace_2416_; lean_object* v_openDecls_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_ngen_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2411_ = lean_st_ref_get(v___y_2409_);
v_env_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_ref(v_env_2412_);
lean_dec(v___x_2411_);
v___x_2413_ = lean_st_ref_get(v___y_2407_);
v_toCold_2414_ = lean_ctor_get(v___y_2408_, 0);
v_mctx_2415_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_mctx_2415_);
lean_dec(v___x_2413_);
v_currNamespace_2416_ = lean_ctor_get(v_toCold_2414_, 4);
v_openDecls_2417_ = lean_ctor_get(v_toCold_2414_, 5);
v___x_2418_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2408_);
v___x_2419_ = lean_st_ref_get(v___y_2409_);
v_ngen_2420_ = lean_ctor_get(v___x_2419_, 2);
lean_inc_ref(v_ngen_2420_);
lean_dec(v___x_2419_);
v___x_2421_ = lean_box(0);
v___x_2422_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_2417_);
lean_inc(v_currNamespace_2416_);
v___x_2423_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2423_, 0, v_env_2412_);
lean_ctor_set(v___x_2423_, 1, v___x_2421_);
lean_ctor_set(v___x_2423_, 2, v___x_2422_);
lean_ctor_set(v___x_2423_, 3, v_mctx_2415_);
lean_ctor_set(v___x_2423_, 4, v___x_2418_);
lean_ctor_set(v___x_2423_, 5, v_currNamespace_2416_);
lean_ctor_set(v___x_2423_, 6, v_openDecls_2417_);
lean_ctor_set(v___x_2423_, 7, v_ngen_2420_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v_toCold_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2463_; 
v___x_2437_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2433_, v___y_2434_, v___y_2435_);
v_toCold_2438_ = lean_ctor_get(v___y_2434_, 0);
v_a_2439_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2441_ = v___x_2437_;
v_isShared_2442_ = v_isSharedCheck_2463_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2437_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2463_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_fileMap_2443_; lean_object* v_env_2444_; lean_object* v_mctx_2445_; lean_object* v_options_2446_; lean_object* v_currNamespace_2447_; lean_object* v_openDecls_2448_; lean_object* v_ngen_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2460_; 
v_fileMap_2443_ = lean_ctor_get(v_toCold_2438_, 1);
v_env_2444_ = lean_ctor_get(v_a_2439_, 0);
v_mctx_2445_ = lean_ctor_get(v_a_2439_, 3);
v_options_2446_ = lean_ctor_get(v_a_2439_, 4);
v_currNamespace_2447_ = lean_ctor_get(v_a_2439_, 5);
v_openDecls_2448_ = lean_ctor_get(v_a_2439_, 6);
v_ngen_2449_ = lean_ctor_get(v_a_2439_, 7);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_a_2439_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; lean_object* v_unused_2462_; 
v_unused_2461_ = lean_ctor_get(v_a_2439_, 2);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_a_2439_, 1);
lean_dec(v_unused_2462_);
v___x_2451_ = v_a_2439_;
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_ngen_2449_);
lean_inc(v_openDecls_2448_);
lean_inc(v_currNamespace_2447_);
lean_inc(v_options_2446_);
lean_inc(v_mctx_2445_);
lean_inc(v_env_2444_);
lean_dec(v_a_2439_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = lean_box(0);
lean_inc_ref(v_fileMap_2443_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 2, v_fileMap_2443_);
lean_ctor_set(v___x_2451_, 1, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_env_2444_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_fileMap_2443_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_mctx_2445_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_options_2446_);
lean_ctor_set(v_reuseFailAlloc_2459_, 5, v_currNamespace_2447_);
lean_ctor_set(v_reuseFailAlloc_2459_, 6, v_openDecls_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 7, v_ngen_2449_);
v___x_2455_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2457_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2455_);
v___x_2457_ = v___x_2441_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11___boxed(lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2489_; 
v___x_2479_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_a_2480_);
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2485_);
v___x_2487_ = v___x_2482_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed(lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(lean_object* v___x_2498_, lean_object* v_ctx_x3f_2499_, size_t v_sz_2500_, size_t v_i_2501_, lean_object* v_bs_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_lt(v_i_2501_, v_sz_2500_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
lean_dec_ref(v_ctx_x3f_2499_);
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_bs_2502_);
return v___x_2511_;
}
else
{
lean_object* v_assignment_2512_; lean_object* v_v_2513_; lean_object* v___x_2514_; lean_object* v_bs_x27_2515_; lean_object* v_a_2517_; lean_object* v_tree_2522_; lean_object* v___x_2523_; 
v_assignment_2512_ = lean_ctor_get(v___x_2498_, 0);
v_v_2513_ = lean_array_uget(v_bs_2502_, v_i_2501_);
v___x_2514_ = lean_unsigned_to_nat(0u);
v_bs_x27_2515_ = lean_array_uset(v_bs_2502_, v_i_2501_, v___x_2514_);
v_tree_2522_ = l_Lean_Elab_InfoTree_substitute(v_v_2513_, v_assignment_2512_);
lean_inc_ref(v_ctx_x3f_2499_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
v___x_2523_ = lean_apply_7(v_ctx_x3f_2499_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, lean_box(0));
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
if (lean_obj_tag(v_a_2524_) == 0)
{
v_a_2517_ = v_tree_2522_;
goto v___jp_2516_;
}
else
{
lean_object* v_val_2525_; lean_object* v___x_2526_; 
v_val_2525_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v_a_2524_, 1);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_val_2525_);
lean_ctor_set(v___x_2526_, 1, v_tree_2522_);
v_a_2517_ = v___x_2526_;
goto v___jp_2516_;
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v_tree_2522_);
lean_dec_ref(v_bs_x27_2515_);
lean_dec_ref(v_ctx_x3f_2499_);
v_a_2527_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2523_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2523_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
v___jp_2516_:
{
size_t v___x_2518_; size_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((size_t)1ULL);
v___x_2519_ = lean_usize_add(v_i_2501_, v___x_2518_);
v___x_2520_ = lean_array_uset(v_bs_x27_2515_, v_i_2501_, v_a_2517_);
v_i_2501_ = v___x_2519_;
v_bs_2502_ = v___x_2520_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27___boxed(lean_object* v___x_2535_, lean_object* v_ctx_x3f_2536_, lean_object* v_sz_2537_, lean_object* v_i_2538_, lean_object* v_bs_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
size_t v_sz_boxed_2547_; size_t v_i_boxed_2548_; lean_object* v_res_2549_; 
v_sz_boxed_2547_ = lean_unbox_usize(v_sz_2537_);
lean_dec(v_sz_2537_);
v_i_boxed_2548_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_res_2549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2535_, v_ctx_x3f_2536_, v_sz_boxed_2547_, v_i_boxed_2548_, v_bs_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec_ref(v___x_2535_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(lean_object* v___x_2550_, lean_object* v_ctx_x3f_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
if (lean_obj_tag(v_x_2552_) == 0)
{
lean_object* v_cs_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2586_; 
v_cs_2560_ = lean_ctor_get(v_x_2552_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_x_2552_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2562_ = v_x_2552_;
v_isShared_2563_ = v_isSharedCheck_2586_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_cs_2560_);
lean_dec(v_x_2552_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2586_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
size_t v_sz_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v_sz_2564_ = lean_array_size(v_cs_2560_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2550_, v_ctx_x3f_2551_, v_sz_2564_, v___x_2565_, v_cs_2560_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2577_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2577_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2577_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_a_2567_);
v___x_2572_ = v___x_2562_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2574_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2572_);
v___x_2574_ = v___x_2569_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_del_object(v___x_2562_);
v_a_2578_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2566_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2566_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
else
{
lean_object* v_vs_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2613_; 
v_vs_2587_ = lean_ctor_get(v_x_2552_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_x_2552_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2589_ = v_x_2552_;
v_isShared_2590_ = v_isSharedCheck_2613_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_vs_2587_);
lean_dec(v_x_2552_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2613_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
size_t v_sz_2591_; size_t v___x_2592_; lean_object* v___x_2593_; 
v_sz_2591_ = lean_array_size(v_vs_2587_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2550_, v_ctx_x3f_2551_, v_sz_2591_, v___x_2592_, v_vs_2587_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2604_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2604_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2604_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_a_2594_);
v___x_2599_ = v___x_2589_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2603_;
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
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
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
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_del_object(v___x_2589_);
v_a_2605_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2593_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2593_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(lean_object* v___x_2614_, lean_object* v_ctx_x3f_2615_, size_t v_sz_2616_, size_t v_i_2617_, lean_object* v_bs_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_lt(v_i_2617_, v_sz_2616_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v_ctx_x3f_2615_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_bs_2618_);
return v___x_2627_;
}
else
{
lean_object* v_v_2628_; lean_object* v___x_2629_; lean_object* v_bs_x27_2630_; lean_object* v___x_2631_; 
v_v_2628_ = lean_array_uget(v_bs_2618_, v_i_2617_);
v___x_2629_ = lean_unsigned_to_nat(0u);
v_bs_x27_2630_ = lean_array_uset(v_bs_2618_, v_i_2617_, v___x_2629_);
lean_inc_ref(v_ctx_x3f_2615_);
v___x_2631_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2614_, v_ctx_x3f_2615_, v_v_2628_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = ((size_t)1ULL);
v___x_2634_ = lean_usize_add(v_i_2617_, v___x_2633_);
v___x_2635_ = lean_array_uset(v_bs_x27_2630_, v_i_2617_, v_a_2632_);
v_i_2617_ = v___x_2634_;
v_bs_2618_ = v___x_2635_;
goto _start;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_bs_x27_2630_);
lean_dec_ref(v_ctx_x3f_2615_);
v_a_2637_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2631_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2631_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28___boxed(lean_object* v___x_2645_, lean_object* v_ctx_x3f_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_bs_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
size_t v_sz_boxed_2657_; size_t v_i_boxed_2658_; lean_object* v_res_2659_; 
v_sz_boxed_2657_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2658_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2645_, v_ctx_x3f_2646_, v_sz_boxed_2657_, v_i_boxed_2658_, v_bs_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___x_2645_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26___boxed(lean_object* v___x_2660_, lean_object* v_ctx_x3f_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2660_, v_ctx_x3f_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v___x_2660_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(lean_object* v___x_2671_, lean_object* v_ctx_x3f_2672_, lean_object* v_t_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_root_2681_; lean_object* v_tail_2682_; lean_object* v_size_2683_; size_t v_shift_2684_; lean_object* v_tailOff_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2721_; 
v_root_2681_ = lean_ctor_get(v_t_2673_, 0);
v_tail_2682_ = lean_ctor_get(v_t_2673_, 1);
v_size_2683_ = lean_ctor_get(v_t_2673_, 2);
v_shift_2684_ = lean_ctor_get_usize(v_t_2673_, 4);
v_tailOff_2685_ = lean_ctor_get(v_t_2673_, 3);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_t_2673_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2687_ = v_t_2673_;
v_isShared_2688_ = v_isSharedCheck_2721_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_tailOff_2685_);
lean_inc(v_size_2683_);
lean_inc(v_tail_2682_);
lean_inc(v_root_2681_);
lean_dec(v_t_2673_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2721_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; 
lean_inc_ref(v_ctx_x3f_2672_);
v___x_2689_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2671_, v_ctx_x3f_2672_, v_root_2681_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; size_t v_sz_2691_; size_t v___x_2692_; lean_object* v___x_2693_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v_sz_2691_ = lean_array_size(v_tail_2682_);
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2671_, v_ctx_x3f_2672_, v_sz_2691_, v___x_2692_, v_tail_2682_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2704_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v_a_2694_);
lean_ctor_set(v___x_2687_, 0, v_a_2690_);
v___x_2699_ = v___x_2687_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2690_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_a_2694_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_size_2683_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_tailOff_2685_);
lean_ctor_set_usize(v_reuseFailAlloc_2703_, 4, v_shift_2684_);
v___x_2699_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2699_);
v___x_2701_ = v___x_2696_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_a_2690_);
lean_del_object(v___x_2687_);
lean_dec(v_tailOff_2685_);
lean_dec(v_size_2683_);
v_a_2705_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2693_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2693_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_del_object(v___x_2687_);
lean_dec(v_tailOff_2685_);
lean_dec(v_size_2683_);
lean_dec_ref(v_tail_2682_);
lean_dec_ref(v_ctx_x3f_2672_);
v_a_2713_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2689_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2689_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22___boxed(lean_object* v___x_2722_, lean_object* v_ctx_x3f_2723_, lean_object* v_t_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v___x_2722_, v_ctx_x3f_2723_, v_t_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___x_2722_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(lean_object* v___y_2733_, lean_object* v_ctx_x3f_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v_a_2740_, lean_object* v_a_x3f_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v_infoState_2744_; lean_object* v_trees_2745_; lean_object* v___x_2746_; 
v___x_2743_ = lean_st_ref_get(v___y_2733_);
v_infoState_2744_ = lean_ctor_get(v___x_2743_, 8);
lean_inc_ref(v_infoState_2744_);
lean_dec(v___x_2743_);
v_trees_2745_ = lean_ctor_get(v_infoState_2744_, 2);
lean_inc_ref(v_trees_2745_);
v___x_2746_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v_infoState_2744_, v_ctx_x3f_2734_, v_trees_2745_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2733_);
lean_dec_ref(v_infoState_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2786_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2786_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2786_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v_infoState_2752_; lean_object* v_env_2753_; lean_object* v_nextMacroScope_2754_; lean_object* v_ngen_2755_; lean_object* v_auxDeclNGen_2756_; lean_object* v_traceState_2757_; lean_object* v_cache_2758_; lean_object* v_recordedDeps_2759_; lean_object* v_messages_2760_; lean_object* v_snapshotTasks_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2785_; 
v___x_2751_ = lean_st_ref_take(v___y_2733_);
v_infoState_2752_ = lean_ctor_get(v___x_2751_, 8);
v_env_2753_ = lean_ctor_get(v___x_2751_, 0);
v_nextMacroScope_2754_ = lean_ctor_get(v___x_2751_, 1);
v_ngen_2755_ = lean_ctor_get(v___x_2751_, 2);
v_auxDeclNGen_2756_ = lean_ctor_get(v___x_2751_, 3);
v_traceState_2757_ = lean_ctor_get(v___x_2751_, 4);
v_cache_2758_ = lean_ctor_get(v___x_2751_, 5);
v_recordedDeps_2759_ = lean_ctor_get(v___x_2751_, 6);
v_messages_2760_ = lean_ctor_get(v___x_2751_, 7);
v_snapshotTasks_2761_ = lean_ctor_get(v___x_2751_, 9);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2763_ = v___x_2751_;
v_isShared_2764_ = v_isSharedCheck_2785_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_snapshotTasks_2761_);
lean_inc(v_infoState_2752_);
lean_inc(v_messages_2760_);
lean_inc(v_recordedDeps_2759_);
lean_inc(v_cache_2758_);
lean_inc(v_traceState_2757_);
lean_inc(v_auxDeclNGen_2756_);
lean_inc(v_ngen_2755_);
lean_inc(v_nextMacroScope_2754_);
lean_inc(v_env_2753_);
lean_dec(v___x_2751_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2785_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
uint8_t v_enabled_2765_; lean_object* v_assignment_2766_; lean_object* v_lazyAssignment_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2783_; 
v_enabled_2765_ = lean_ctor_get_uint8(v_infoState_2752_, sizeof(void*)*3);
v_assignment_2766_ = lean_ctor_get(v_infoState_2752_, 0);
v_lazyAssignment_2767_ = lean_ctor_get(v_infoState_2752_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_infoState_2752_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; 
v_unused_2784_ = lean_ctor_get(v_infoState_2752_, 2);
lean_dec(v_unused_2784_);
v___x_2769_ = v_infoState_2752_;
v_isShared_2770_ = v_isSharedCheck_2783_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_lazyAssignment_2767_);
lean_inc(v_assignment_2766_);
lean_dec(v_infoState_2752_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2783_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Lean_PersistentArray_append___redArg(v_a_2740_, v_a_2747_);
lean_dec(v_a_2747_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 2, v___x_2772_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_assignment_2766_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_lazyAssignment_2767_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v___x_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2782_, sizeof(void*)*3, v_enabled_2765_);
v___x_2774_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 8, v___x_2774_);
v___x_2776_ = v___x_2763_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_env_2753_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_nextMacroScope_2754_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_ngen_2755_);
lean_ctor_set(v_reuseFailAlloc_2781_, 3, v_auxDeclNGen_2756_);
lean_ctor_set(v_reuseFailAlloc_2781_, 4, v_traceState_2757_);
lean_ctor_set(v_reuseFailAlloc_2781_, 5, v_cache_2758_);
lean_ctor_set(v_reuseFailAlloc_2781_, 6, v_recordedDeps_2759_);
lean_ctor_set(v_reuseFailAlloc_2781_, 7, v_messages_2760_);
lean_ctor_set(v_reuseFailAlloc_2781_, 8, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 9, v_snapshotTasks_2761_);
v___x_2776_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = lean_st_ref_put(v___y_2733_, v___x_2776_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2771_);
v___x_2779_ = v___x_2749_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2771_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_a_2740_);
v_a_2787_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2746_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2746_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v___y_2795_, lean_object* v_ctx_x3f_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v_a_2802_, lean_object* v_a_x3f_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2795_, v_ctx_x3f_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v_a_2802_, v_a_x3f_2803_);
lean_dec(v_a_x3f_2803_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2795_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v_infoState_2809_; lean_object* v_trees_2810_; lean_object* v___x_2811_; lean_object* v_infoState_2812_; lean_object* v_env_2813_; lean_object* v_nextMacroScope_2814_; lean_object* v_ngen_2815_; lean_object* v_auxDeclNGen_2816_; lean_object* v_traceState_2817_; lean_object* v_cache_2818_; lean_object* v_recordedDeps_2819_; lean_object* v_messages_2820_; lean_object* v_snapshotTasks_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2844_; 
v___x_2808_ = lean_st_ref_get(v___y_2806_);
v_infoState_2809_ = lean_ctor_get(v___x_2808_, 8);
lean_inc_ref(v_infoState_2809_);
lean_dec(v___x_2808_);
v_trees_2810_ = lean_ctor_get(v_infoState_2809_, 2);
lean_inc_ref(v_trees_2810_);
lean_dec_ref(v_infoState_2809_);
v___x_2811_ = lean_st_ref_take(v___y_2806_);
v_infoState_2812_ = lean_ctor_get(v___x_2811_, 8);
v_env_2813_ = lean_ctor_get(v___x_2811_, 0);
v_nextMacroScope_2814_ = lean_ctor_get(v___x_2811_, 1);
v_ngen_2815_ = lean_ctor_get(v___x_2811_, 2);
v_auxDeclNGen_2816_ = lean_ctor_get(v___x_2811_, 3);
v_traceState_2817_ = lean_ctor_get(v___x_2811_, 4);
v_cache_2818_ = lean_ctor_get(v___x_2811_, 5);
v_recordedDeps_2819_ = lean_ctor_get(v___x_2811_, 6);
v_messages_2820_ = lean_ctor_get(v___x_2811_, 7);
v_snapshotTasks_2821_ = lean_ctor_get(v___x_2811_, 9);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2823_ = v___x_2811_;
v_isShared_2824_ = v_isSharedCheck_2844_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snapshotTasks_2821_);
lean_inc(v_infoState_2812_);
lean_inc(v_messages_2820_);
lean_inc(v_recordedDeps_2819_);
lean_inc(v_cache_2818_);
lean_inc(v_traceState_2817_);
lean_inc(v_auxDeclNGen_2816_);
lean_inc(v_ngen_2815_);
lean_inc(v_nextMacroScope_2814_);
lean_inc(v_env_2813_);
lean_dec(v___x_2811_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2844_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint8_t v_enabled_2825_; lean_object* v_assignment_2826_; lean_object* v_lazyAssignment_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2842_; 
v_enabled_2825_ = lean_ctor_get_uint8(v_infoState_2812_, sizeof(void*)*3);
v_assignment_2826_ = lean_ctor_get(v_infoState_2812_, 0);
v_lazyAssignment_2827_ = lean_ctor_get(v_infoState_2812_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_infoState_2812_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_infoState_2812_, 2);
lean_dec(v_unused_2843_);
v___x_2829_ = v_infoState_2812_;
v_isShared_2830_ = v_isSharedCheck_2842_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_lazyAssignment_2827_);
lean_inc(v_assignment_2826_);
lean_dec(v_infoState_2812_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2842_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2831_ = lean_unsigned_to_nat(32u);
v___x_2832_ = lean_mk_empty_array_with_capacity(v___x_2831_);
lean_dec_ref(v___x_2832_);
v___x_2833_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 2, v___x_2833_);
v___x_2835_ = v___x_2829_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_assignment_2826_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_lazyAssignment_2827_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v___x_2833_);
lean_ctor_set_uint8(v_reuseFailAlloc_2841_, sizeof(void*)*3, v_enabled_2825_);
v___x_2835_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2837_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 8, v___x_2835_);
v___x_2837_ = v___x_2823_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_env_2813_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_nextMacroScope_2814_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_ngen_2815_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_auxDeclNGen_2816_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_traceState_2817_);
lean_ctor_set(v_reuseFailAlloc_2840_, 5, v_cache_2818_);
lean_ctor_set(v_reuseFailAlloc_2840_, 6, v_recordedDeps_2819_);
lean_ctor_set(v_reuseFailAlloc_2840_, 7, v_messages_2820_);
lean_ctor_set(v_reuseFailAlloc_2840_, 8, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2840_, 9, v_snapshotTasks_2821_);
v___x_2837_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_st_ref_put(v___y_2806_, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_trees_2810_);
return v___x_2839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg___boxed(lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2845_);
lean_dec(v___y_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(lean_object* v_x_2848_, lean_object* v_ctx_x3f_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; lean_object* v_infoState_2858_; uint8_t v_enabled_2859_; 
v___x_2857_ = lean_st_ref_get(v___y_2855_);
v_infoState_2858_ = lean_ctor_get(v___x_2857_, 8);
lean_inc_ref(v_infoState_2858_);
lean_dec(v___x_2857_);
v_enabled_2859_ = lean_ctor_get_uint8(v_infoState_2858_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2858_);
if (v_enabled_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v_ctx_x3f_2849_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
v___x_2860_ = lean_apply_7(v_x_2848_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, lean_box(0));
return v___x_2860_;
}
else
{
lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v_r_2863_; 
v___x_2861_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2855_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2861_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
v_r_2863_ = lean_apply_7(v_x_2848_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, lean_box(0));
if (lean_obj_tag(v_r_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2888_; 
v_a_2864_ = lean_ctor_get(v_r_2863_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_r_2863_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2866_ = v_r_2863_;
v_isShared_2867_ = v_isSharedCheck_2888_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v_r_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2888_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
lean_inc(v_a_2864_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set_tag(v___x_2866_, 1);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2855_, v_ctx_x3f_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v_a_2862_, v___x_2869_);
lean_dec_ref(v___x_2869_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; 
v_unused_2878_ = lean_ctor_get(v___x_2870_, 0);
lean_dec(v_unused_2878_);
v___x_2872_ = v___x_2870_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v___x_2870_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v_a_2864_);
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2864_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_a_2864_);
v_a_2879_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2870_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2870_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v_r_2863_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v_r_2863_, 1);
v___x_2890_ = lean_box(0);
v___x_2891_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2855_, v_ctx_x3f_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v_a_2862_, v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2891_, 0);
lean_dec(v_unused_2899_);
v___x_2893_ = v___x_2891_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_dec(v___x_2891_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 1);
lean_ctor_set(v___x_2893_, 0, v_a_2889_);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2889_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_a_2889_);
v_a_2900_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2891_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2891_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___boxed(lean_object* v_x_2908_, lean_object* v_ctx_x3f_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2908_, v_ctx_x3f_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(lean_object* v_x_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___f_2927_; lean_object* v___x_2928_; 
v___f_2927_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0));
v___x_2928_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2919_, v___f_2927_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___boxed(lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(lean_object* v_00_u03b1_2938_, lean_object* v_x_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed(lean_object* v_00_u03b1_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(v_00_u03b1_2948_, v_x_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2957_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__1(void){
_start:
{
lean_object* v_fields_2960_; lean_object* v_seenFields_2961_; lean_object* v___x_2962_; 
v_fields_2960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v_seenFields_2961_ = l_Lean_NameSet_empty;
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_seenFields_2961_);
lean_ctor_set(v___x_2962_, 1, v_fields_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__2(void){
_start:
{
lean_object* v___x_2963_; lean_object* v_source_x3f_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__1, &l_Lean_Elab_Tactic_elabConfig___closed__1_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__1);
v_source_x3f_2964_ = lean_box(0);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_source_x3f_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t v_recover_2968_, lean_object* v_structName_2969_, lean_object* v_items_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; size_t v_sz_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___f_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2978_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___closed__0));
v___x_2980_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__2, &l_Lean_Elab_Tactic_elabConfig___closed__2_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__2);
v_sz_2981_ = lean_array_size(v_items_2970_);
v___x_2982_ = lean_box(v_recover_2968_);
v___x_2983_ = lean_box_usize(v_sz_2981_);
v___x_2984_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___boxed__const__1));
v___f_2985_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabConfig___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2985_, 0, v_structName_2969_);
lean_closure_set(v___f_2985_, 1, v___x_2982_);
lean_closure_set(v___f_2985_, 2, v_items_2970_);
lean_closure_set(v___f_2985_, 3, v___x_2983_);
lean_closure_set(v___f_2985_, 4, v___x_2984_);
lean_closure_set(v___f_2985_, 5, v___x_2980_);
v___x_2986_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed), 9, 2);
lean_closure_set(v___x_2986_, 0, lean_box(0));
lean_closure_set(v___x_2986_, 1, v___f_2985_);
v___x_2987_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed), 11, 4);
lean_closure_set(v___x_2987_, 0, lean_box(0));
lean_closure_set(v___x_2987_, 1, v___x_2978_);
lean_closure_set(v___x_2987_, 2, v___x_2979_);
lean_closure_set(v___x_2987_, 3, v___x_2986_);
v___x_2988_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v___x_2987_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___boxed(lean_object* v_recover_2989_, lean_object* v_structName_2990_, lean_object* v_items_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
uint8_t v_recover_boxed_2999_; lean_object* v_res_3000_; 
v_recover_boxed_2999_ = lean_unbox(v_recover_2989_);
v_res_3000_ = l_Lean_Elab_Tactic_elabConfig(v_recover_boxed_2999_, v_structName_2990_, v_items_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(lean_object* v_00_u03b1_3001_, lean_object* v_ref_3002_, lean_object* v_msg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_3002_, v_msg_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_ref_3013_, lean_object* v_msg_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(v_00_u03b1_3012_, v_ref_3013_, v_msg_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v_ref_3013_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(lean_object* v_t_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_3023_, v___y_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___boxed(lean_object* v_t_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(v_t_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(lean_object* v_00_u03b1_3041_, lean_object* v_constName_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3051_, lean_object* v_constName_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(v_00_u03b1_3051_, v_constName_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(lean_object* v_00_u03b1_3061_, lean_object* v_msg_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3071_, lean_object* v_msg_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(v_00_u03b1_3071_, v_msg_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___boxed(lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___boxed(lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(lean_object* v_00_u03b1_3113_, lean_object* v_x_3114_, lean_object* v_ctx_x3f_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_3114_, v_ctx_x3f_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3124_, lean_object* v_x_3125_, lean_object* v_ctx_x3f_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(v_00_u03b1_3124_, v_x_3125_, v_ctx_x3f_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(lean_object* v_ref_3135_, lean_object* v_msgData_3136_, uint8_t v_severity_3137_, uint8_t v_isSilent_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_3135_, v_msgData_3136_, v_severity_3137_, v_isSilent_3138_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___boxed(lean_object* v_ref_3147_, lean_object* v_msgData_3148_, lean_object* v_severity_3149_, lean_object* v_isSilent_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
uint8_t v_severity_boxed_3158_; uint8_t v_isSilent_boxed_3159_; lean_object* v_res_3160_; 
v_severity_boxed_3158_ = lean_unbox(v_severity_3149_);
v_isSilent_boxed_3159_ = lean_unbox(v_isSilent_3150_);
v_res_3160_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(v_ref_3147_, v_msgData_3148_, v_severity_boxed_3158_, v_isSilent_boxed_3159_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v_ref_3147_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(lean_object* v_00_u03b1_3161_, lean_object* v_ref_3162_, lean_object* v_constName_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_3162_, v_constName_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b1_3172_, lean_object* v_ref_3173_, lean_object* v_constName_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(v_00_u03b1_3172_, v_ref_3173_, v_constName_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(lean_object* v_msgData_3183_, lean_object* v_macroStack_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_3183_, v_macroStack_3184_, v___y_3189_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___boxed(lean_object* v_msgData_3193_, lean_object* v_macroStack_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(v_msgData_3193_, v_macroStack_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(lean_object* v_00_u03b1_3203_, lean_object* v_ref_3204_, lean_object* v_msg_3205_, lean_object* v_declHint_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_3204_, v_msg_3205_, v_declHint_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___boxed(lean_object* v_00_u03b1_3215_, lean_object* v_ref_3216_, lean_object* v_msg_3217_, lean_object* v_declHint_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(v_00_u03b1_3215_, v_ref_3216_, v_msg_3217_, v_declHint_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v_ref_3216_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(lean_object* v_msg_3227_, lean_object* v_declHint_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_3227_, v_declHint_3228_, v___y_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___boxed(lean_object* v_msg_3237_, lean_object* v_declHint_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(v_msg_3237_, v_declHint_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
return v_res_3246_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11));
v___x_3280_ = l_String_toRawSubstring_x27(v___x_3279_);
return v___x_3280_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18));
v___x_3297_ = l_String_toRawSubstring_x27(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21));
v___x_3302_ = l_String_toRawSubstring_x27(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31));
v___x_3327_ = l_String_toRawSubstring_x27(v___x_3326_);
return v___x_3327_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39));
v___x_3349_ = l_String_toRawSubstring_x27(v___x_3348_);
return v___x_3349_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48));
v___x_3372_ = l_String_toRawSubstring_x27(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3383_ = l_String_toRawSubstring_x27(v___x_3382_);
return v___x_3383_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71));
v___x_3427_ = l_String_toRawSubstring_x27(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77));
v___x_3439_ = l_String_toRawSubstring_x27(v___x_3438_);
return v___x_3439_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83));
v___x_3454_ = l_String_toRawSubstring_x27(v___x_3453_);
return v___x_3454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89));
v___x_3470_ = l_String_toRawSubstring_x27(v___x_3469_);
return v___x_3470_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114));
v___x_3538_ = l_String_toRawSubstring_x27(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117));
v___x_3543_ = l_String_toRawSubstring_x27(v___x_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122));
v___x_3553_ = l_String_toRawSubstring_x27(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128));
v___x_3567_ = l_String_toRawSubstring_x27(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131));
v___x_3572_ = l_String_toRawSubstring_x27(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139));
v___x_3594_ = l_String_toRawSubstring_x27(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150));
v___x_3623_ = l_String_toRawSubstring_x27(v___x_3622_);
return v___x_3623_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168));
v___x_3664_ = l_String_toRawSubstring_x27(v___x_3663_);
return v___x_3664_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175));
v___x_3680_ = l_String_toRawSubstring_x27(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190));
v___x_3703_ = l_String_toRawSubstring_x27(v___x_3702_);
return v___x_3703_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198));
v___x_3722_ = l_String_toRawSubstring_x27(v___x_3721_);
return v___x_3722_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17));
v___x_3726_ = l_String_toRawSubstring_x27(v___x_3725_);
return v___x_3726_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209));
v___x_3749_ = l_String_toRawSubstring_x27(v___x_3748_);
return v___x_3749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213(void){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212));
v___x_3754_ = l_String_toRawSubstring_x27(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220));
v___x_3775_ = l_String_toRawSubstring_x27(v___x_3774_);
return v___x_3775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224));
v___x_3782_ = l_String_toRawSubstring_x27(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232));
v___x_3797_ = l_String_toRawSubstring_x27(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238));
v___x_3809_ = l_String_toRawSubstring_x27(v___x_3808_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242));
v___x_3815_ = l_String_toRawSubstring_x27(v___x_3814_);
return v___x_3815_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246));
v___x_3821_ = l_String_toRawSubstring_x27(v___x_3820_);
return v___x_3821_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253));
v___x_3836_ = l_String_toRawSubstring_x27(v___x_3835_);
return v___x_3836_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15));
v___x_3842_ = l_String_toRawSubstring_x27(v___x_3841_);
return v___x_3842_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261));
v___x_3853_ = l_String_toRawSubstring_x27(v___x_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(lean_object* v_doc_x3f_3868_, lean_object* v_elabName_3869_, lean_object* v_type_3870_, lean_object* v_monadName_3871_, lean_object* v_adapt_3872_, lean_object* v_recover_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_quotContext_3876_; lean_object* v_currMacroScope_3877_; lean_object* v_ref_3878_; lean_object* v_ref_3879_; uint8_t v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___y_4016_; 
v_quotContext_3876_ = lean_ctor_get(v_a_3874_, 1);
v_currMacroScope_3877_ = lean_ctor_get(v_a_3874_, 2);
v_ref_3878_ = lean_ctor_get(v_a_3874_, 5);
v_ref_3879_ = l_Lean_replaceRef(v_type_3870_, v_ref_3878_);
v___x_3880_ = 0;
v___x_3881_ = l_Lean_SourceInfo_fromRef(v_ref_3879_, v___x_3880_);
lean_dec(v_ref_3879_);
v___x_3882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_3883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_3881_, 7);
v___x_3884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3881_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_3886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_3887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3881_);
lean_ctor_set(v___x_3887_, 1, v___x_3885_);
lean_ctor_set(v___x_3887_, 2, v___x_3886_);
v___x_3888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
lean_inc_ref_n(v___x_3887_, 2);
v___x_3889_ = l_Lean_Syntax_node1(v___x_3881_, v___x_3888_, v___x_3887_);
v___x_3890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_3891_ = l_Lean_Syntax_node1(v___x_3881_, v___x_3890_, v___x_3887_);
v___x_3892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_3893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3881_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
lean_inc_n(v_type_3870_, 3);
v___x_3894_ = l_Lean_Syntax_node2(v___x_3881_, v___x_3885_, v___x_3893_, v_type_3870_);
v___x_3895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_3896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3881_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = l_Lean_Syntax_node6(v___x_3881_, v___x_3882_, v___x_3884_, v___x_3887_, v___x_3889_, v___x_3891_, v___x_3894_, v___x_3896_);
v___x_3898_ = l_Lean_SourceInfo_fromRef(v_ref_3878_, v___x_3880_);
v___x_3899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1));
v___x_3900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3));
lean_inc_n(v___x_3898_, 55);
v___x_3901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3898_);
lean_ctor_set(v___x_3901_, 1, v___x_3885_);
lean_ctor_set(v___x_3901_, 2, v___x_3886_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5));
v___x_3904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3898_);
lean_ctor_set(v___x_3904_, 1, v___x_3902_);
v___x_3905_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3903_, v___x_3904_);
v___x_3906_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3905_);
lean_inc_ref_n(v___x_3901_, 21);
v___x_3907_ = l_Lean_Syntax_node7(v___x_3898_, v___x_3900_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3906_, v___x_3901_);
v___x_3908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7));
v___x_3909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8));
v___x_3910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3898_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10));
v___x_3912_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12);
v___x_3913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13));
lean_inc_n(v_currMacroScope_3877_, 9);
lean_inc_n(v_quotContext_3876_, 9);
v___x_3914_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3913_, v_currMacroScope_3877_);
v___x_3915_ = lean_box(0);
v___x_3916_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3898_);
lean_ctor_set(v___x_3916_, 1, v___x_3912_);
lean_ctor_set(v___x_3916_, 2, v___x_3914_);
lean_ctor_set(v___x_3916_, 3, v___x_3915_);
lean_inc_ref(v___x_3916_);
v___x_3917_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3911_, v___x_3916_, v___x_3901_);
v___x_3918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15));
v___x_3919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17));
v___x_3920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
v___x_3921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3898_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19);
v___x_3923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20));
v___x_3924_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3923_, v_currMacroScope_3877_);
v___x_3925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3898_);
lean_ctor_set(v___x_3925_, 1, v___x_3922_);
lean_ctor_set(v___x_3925_, 2, v___x_3924_);
lean_ctor_set(v___x_3925_, 3, v___x_3915_);
lean_inc_ref(v___x_3925_);
v___x_3926_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3898_);
lean_ctor_set(v___x_3927_, 1, v___x_3892_);
v___x_3928_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22);
v___x_3929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23));
v___x_3930_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3929_, v_currMacroScope_3877_);
v___x_3931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28));
v___x_3932_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3898_);
lean_ctor_set(v___x_3932_, 1, v___x_3928_);
lean_ctor_set(v___x_3932_, 2, v___x_3930_);
lean_ctor_set(v___x_3932_, 3, v___x_3931_);
lean_inc_ref_n(v___x_3927_, 2);
v___x_3933_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_3927_, v___x_3932_);
v___x_3934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_3935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3898_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
lean_inc_ref_n(v___x_3935_, 2);
lean_inc_ref_n(v___x_3921_, 2);
v___x_3936_ = l_Lean_Syntax_node5(v___x_3898_, v___x_3919_, v___x_3921_, v___x_3926_, v___x_3933_, v___x_3901_, v___x_3935_);
v___x_3937_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3936_);
v___x_3938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30));
v___x_3939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_3940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32);
v___x_3941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33));
v___x_3942_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3941_, v_currMacroScope_3877_);
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36));
v___x_3944_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3898_);
lean_ctor_set(v___x_3944_, 1, v___x_3940_);
lean_ctor_set(v___x_3944_, 2, v___x_3942_);
lean_ctor_set(v___x_3944_, 3, v___x_3943_);
v___x_3945_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v_type_3870_);
lean_inc(v___x_3945_);
v___x_3946_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_3944_, v___x_3945_);
v___x_3947_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3938_, v___x_3927_, v___x_3946_);
lean_inc(v___x_3947_);
v___x_3948_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3947_);
lean_inc(v___x_3948_);
lean_inc(v___x_3937_);
v___x_3949_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3918_, v___x_3937_, v___x_3948_);
v___x_3950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38));
v___x_3951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_3952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3898_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40);
v___x_3954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42));
v___x_3955_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3954_, v_currMacroScope_3877_);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45));
v___x_3957_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3898_);
lean_ctor_set(v___x_3957_, 1, v___x_3953_);
lean_ctor_set(v___x_3957_, 2, v___x_3955_);
lean_ctor_set(v___x_3957_, 3, v___x_3956_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47));
v___x_3959_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50));
v___x_3961_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3960_, v_currMacroScope_3877_);
v___x_3962_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3898_);
lean_ctor_set(v___x_3962_, 1, v___x_3959_);
lean_ctor_set(v___x_3962_, 2, v___x_3961_);
lean_ctor_set(v___x_3962_, 3, v___x_3915_);
v___x_3963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52));
v___x_3964_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_3965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3898_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54);
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55));
v___x_3968_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3967_, v_currMacroScope_3877_);
v___x_3969_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3898_);
lean_ctor_set(v___x_3969_, 1, v___x_3966_);
lean_ctor_set(v___x_3969_, 2, v___x_3968_);
lean_ctor_set(v___x_3969_, 3, v___x_3915_);
lean_inc_ref(v___x_3965_);
v___x_3970_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3963_, v___x_3965_, v___x_3969_);
lean_inc_ref_n(v___x_3952_, 2);
v___x_3971_ = l_Lean_Syntax_node5(v___x_3898_, v___x_3958_, v___x_3921_, v___x_3962_, v___x_3952_, v___x_3970_, v___x_3935_);
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57));
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3898_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
lean_inc_ref(v___x_3974_);
v___x_3975_ = l_Lean_Syntax_node3(v___x_3898_, v___x_3972_, v___x_3974_, v___x_3974_, v_type_3870_);
lean_inc(v___x_3975_);
v___x_3976_ = l_Lean_Syntax_node4(v___x_3898_, v___x_3885_, v___x_3971_, v_type_3870_, v___x_3975_, v___x_3925_);
v___x_3977_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_3957_, v___x_3976_);
v___x_3978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60));
v___x_3979_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3978_, v___x_3901_, v___x_3901_);
lean_inc(v___x_3979_);
v___x_3980_ = l_Lean_Syntax_node4(v___x_3898_, v___x_3950_, v___x_3952_, v___x_3977_, v___x_3979_, v___x_3901_);
lean_inc_ref(v___x_3910_);
v___x_3981_ = l_Lean_Syntax_node5(v___x_3898_, v___x_3908_, v___x_3910_, v___x_3917_, v___x_3949_, v___x_3980_, v___x_3901_);
v___x_3982_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3899_, v___x_3907_, v___x_3981_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62));
v___x_3984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63));
v___x_3985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3898_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65));
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67));
v___x_3988_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3987_, v___x_3901_);
v___x_3989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70));
v___x_3990_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72);
v___x_3991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73));
v___x_3992_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_3991_, v_currMacroScope_3877_);
v___x_3993_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3898_);
lean_ctor_set(v___x_3993_, 1, v___x_3990_);
lean_ctor_set(v___x_3993_, 2, v___x_3992_);
lean_ctor_set(v___x_3993_, 3, v___x_3915_);
v___x_3994_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3916_);
v___x_3995_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3989_, v___x_3993_, v___x_3994_);
v___x_3996_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3986_, v___x_3988_, v___x_3995_);
v___x_3997_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3996_);
v___x_3998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74));
v___x_3999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3898_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = l_Lean_Syntax_node3(v___x_3898_, v___x_3983_, v___x_3985_, v___x_3997_, v___x_3999_);
v___x_4001_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4000_);
v___x_4002_ = l_Lean_Syntax_node7(v___x_3898_, v___x_3900_, v___x_3901_, v___x_4001_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_);
v___x_4003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75));
v___x_4004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76));
v___x_4005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_3898_);
lean_ctor_set(v___x_4005_, 1, v___x_4003_);
v___x_4006_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78);
v___x_4007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79));
v___x_4008_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4007_, v_currMacroScope_3877_);
v___x_4009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4009_, 0, v___x_3898_);
lean_ctor_set(v___x_4009_, 1, v___x_4006_);
lean_ctor_set(v___x_4009_, 2, v___x_4008_);
lean_ctor_set(v___x_4009_, 3, v___x_3915_);
lean_inc_ref(v___x_4009_);
v___x_4010_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3911_, v___x_4009_, v___x_3901_);
v___x_4011_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81));
v___x_4012_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4011_, v___x_3937_, v___x_3947_);
v___x_4013_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4004_, v___x_4005_, v___x_4010_, v___x_4012_, v___x_3901_);
v___x_4014_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3899_, v___x_4002_, v___x_4013_);
if (lean_obj_tag(v_doc_x3f_3868_) == 1)
{
lean_object* v_val_4346_; lean_object* v___x_4347_; 
v_val_4346_ = lean_ctor_get(v_doc_x3f_3868_, 0);
lean_inc(v_val_4346_);
lean_dec_ref_known(v_doc_x3f_3868_, 1);
v___x_4347_ = l_Array_mkArray1___redArg(v_val_4346_);
v___y_4016_ = v___x_4347_;
goto v___jp_4015_;
}
else
{
lean_object* v___x_4348_; 
lean_dec(v_doc_x3f_3868_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268));
v___y_4016_ = v___x_4348_;
goto v___jp_4015_;
}
v___jp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4017_ = l_Array_append___redArg(v___x_3886_, v___y_4016_);
lean_dec_ref(v___y_4016_);
lean_inc_n(v___x_3898_, 183);
v___x_4018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4018_, 0, v___x_3898_);
lean_ctor_set(v___x_4018_, 1, v___x_3885_);
lean_ctor_set(v___x_4018_, 2, v___x_4017_);
lean_inc_ref_n(v___x_3901_, 57);
v___x_4019_ = l_Lean_Syntax_node7(v___x_3898_, v___x_3900_, v___x_4018_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_, v___x_3901_);
v___x_4020_ = lean_box(2);
v___x_4021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82));
v___x_4022_ = lean_unsigned_to_nat(2u);
v___x_4023_ = lean_mk_empty_array_with_capacity(v___x_4022_);
v___x_4024_ = lean_array_push(v___x_4023_, v_elabName_3869_);
v___x_4025_ = lean_array_push(v___x_4024_, v___x_4021_);
v___x_4026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4020_);
lean_ctor_set(v___x_4026_, 1, v___x_3911_);
lean_ctor_set(v___x_4026_, 2, v___x_4025_);
v___x_4027_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84);
v___x_4028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85));
lean_inc_n(v_currMacroScope_3877_, 26);
lean_inc_n(v_quotContext_3876_, 26);
v___x_4029_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4028_, v_currMacroScope_3877_);
v___x_4030_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88));
v___x_4031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4031_, 0, v___x_3898_);
lean_ctor_set(v___x_4031_, 1, v___x_4027_);
lean_ctor_set(v___x_4031_, 2, v___x_4029_);
lean_ctor_set(v___x_4031_, 3, v___x_4030_);
lean_inc_ref(v___x_4031_);
v___x_4032_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4031_);
v___x_4033_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90);
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91));
v___x_4035_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4034_, v_currMacroScope_3877_);
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96));
v___x_4037_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4037_, 0, v___x_3898_);
lean_ctor_set(v___x_4037_, 1, v___x_4033_);
lean_ctor_set(v___x_4037_, 2, v___x_4035_);
lean_ctor_set(v___x_4037_, 3, v___x_4036_);
lean_inc_ref(v___x_3927_);
v___x_4038_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_3927_, v___x_4037_);
lean_inc_ref_n(v___x_3935_, 3);
lean_inc(v___x_4032_);
lean_inc_ref_n(v___x_3921_, 2);
v___x_4039_ = l_Lean_Syntax_node5(v___x_3898_, v___x_3919_, v___x_3921_, v___x_4032_, v___x_4038_, v___x_3901_, v___x_3935_);
v___x_4040_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4039_);
v___x_4041_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v_monadName_3871_, v___x_3945_);
v___x_4042_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3938_, v___x_3927_, v___x_4041_);
v___x_4043_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4042_);
v___x_4044_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3918_, v___x_4040_, v___x_4043_);
v___x_4045_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97));
v___x_4046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98));
v___x_4047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_3898_);
lean_ctor_set(v___x_4047_, 1, v___x_4045_);
v___x_4048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100));
v___x_4049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102));
v___x_4050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104));
v___x_4051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105));
v___x_4052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_3898_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107));
v___x_4054_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4053_, v___x_3901_);
v___x_4055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109));
v___x_4056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111));
v___x_4057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113));
v___x_4058_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4060_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4059_, v_currMacroScope_3877_);
v___x_4061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4061_, 0, v___x_3898_);
lean_ctor_set(v___x_4061_, 1, v___x_4058_);
lean_ctor_set(v___x_4061_, 2, v___x_4060_);
lean_ctor_set(v___x_4061_, 3, v___x_3915_);
lean_inc_ref(v___x_4061_);
v___x_4062_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4057_, v___x_4061_);
lean_inc_ref_n(v___x_3952_, 5);
v___x_4063_ = l_Lean_Syntax_node5(v___x_3898_, v___x_4056_, v___x_4062_, v___x_3901_, v___x_3901_, v___x_3952_, v_recover_3873_);
v___x_4064_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4055_, v___x_4063_);
lean_inc_n(v___x_4054_, 5);
lean_inc_ref_n(v___x_4052_, 5);
v___x_4065_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4050_, v___x_4052_, v___x_3901_, v___x_4054_, v___x_4064_);
v___x_4066_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4065_, v___x_3901_);
v___x_4067_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118);
v___x_4068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119));
v___x_4069_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4068_, v_currMacroScope_3877_);
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121));
v___x_4071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4071_, 0, v___x_3898_);
lean_ctor_set(v___x_4071_, 1, v___x_4067_);
lean_ctor_set(v___x_4071_, 2, v___x_4069_);
lean_ctor_set(v___x_4071_, 3, v___x_4070_);
lean_inc_ref(v___x_4071_);
v___x_4072_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4057_, v___x_4071_);
v___x_4073_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123);
v___x_4074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124));
v___x_4075_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4074_, v_currMacroScope_3877_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127));
v___x_4077_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4077_, 0, v___x_3898_);
lean_ctor_set(v___x_4077_, 1, v___x_4073_);
lean_ctor_set(v___x_4077_, 2, v___x_4075_);
lean_ctor_set(v___x_4077_, 3, v___x_4076_);
v___x_4078_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129);
v___x_4079_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130));
v___x_4080_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4079_, v_currMacroScope_3877_);
v___x_4081_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4081_, 0, v___x_3898_);
lean_ctor_set(v___x_4081_, 1, v___x_4078_);
lean_ctor_set(v___x_4081_, 2, v___x_4080_);
lean_ctor_set(v___x_4081_, 3, v___x_3915_);
lean_inc_ref(v___x_4081_);
v___x_4082_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4057_, v___x_4081_);
v___x_4083_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132);
v___x_4084_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133));
v___x_4085_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4084_, v_currMacroScope_3877_);
v___x_4086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136));
v___x_4087_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4087_, 0, v___x_3898_);
lean_ctor_set(v___x_4087_, 1, v___x_4083_);
lean_ctor_set(v___x_4087_, 2, v___x_4085_);
lean_ctor_set(v___x_4087_, 3, v___x_4086_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4092_ = lean_box(0);
v___x_4093_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4092_, v_currMacroScope_3877_);
v___x_4094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4095_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4095_, 0, v___x_3898_);
lean_ctor_set(v___x_4095_, 1, v___x_4091_);
lean_ctor_set(v___x_4095_, 2, v___x_4093_);
lean_ctor_set(v___x_4095_, 3, v___x_4094_);
v___x_4096_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4090_, v___x_4095_);
v___x_4097_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4089_, v___x_3921_, v___x_4096_);
v___x_4098_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140);
v___x_4099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141));
v___x_4100_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4099_, v_currMacroScope_3877_);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144));
v___x_4102_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4102_, 0, v___x_3898_);
lean_ctor_set(v___x_4102_, 1, v___x_4098_);
lean_ctor_set(v___x_4102_, 2, v___x_4100_);
lean_ctor_set(v___x_4102_, 3, v___x_4101_);
v___x_4103_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4102_, v___x_4032_);
lean_inc(v___x_4097_);
v___x_4104_ = l_Lean_Syntax_node3(v___x_3898_, v___x_4088_, v___x_4097_, v___x_4103_, v___x_3935_);
v___x_4105_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4104_);
v___x_4106_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4087_, v___x_4105_);
v___x_4107_ = l_Lean_Syntax_node5(v___x_3898_, v___x_4056_, v___x_4082_, v___x_3901_, v___x_3901_, v___x_3952_, v___x_4106_);
v___x_4108_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4055_, v___x_4107_);
v___x_4109_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4050_, v___x_4052_, v___x_3901_, v___x_4054_, v___x_4108_);
v___x_4110_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4109_, v___x_3901_);
v___x_4111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146));
v___x_4112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147));
v___x_4113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_3898_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149));
v___x_4115_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151);
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153));
v___x_4117_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4116_, v_currMacroScope_3877_);
v___x_4118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4118_, 0, v___x_3898_);
lean_ctor_set(v___x_4118_, 1, v___x_4115_);
lean_ctor_set(v___x_4118_, 2, v___x_4117_);
lean_ctor_set(v___x_4118_, 3, v___x_3915_);
v___x_4119_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4114_, v___x_3901_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154));
v___x_4121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_3898_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156));
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157));
v___x_4124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_3898_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3897_);
lean_inc_ref(v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4122_, v___x_4124_, v___x_4125_);
v___x_4127_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4126_, v___x_3901_);
lean_inc(v___x_4127_);
v___x_4128_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4127_);
v___x_4129_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4128_);
lean_inc(v___x_4129_);
lean_inc_ref_n(v___x_4121_, 3);
lean_inc_ref_n(v___x_4113_, 3);
v___x_4130_ = l_Lean_Syntax_node6(v___x_3898_, v___x_4111_, v___x_4113_, v___x_4119_, v___x_4121_, v___x_4129_, v___x_3901_, v___x_3901_);
v___x_4131_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4130_, v___x_3901_);
v___x_4132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159));
v___x_4133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160));
v___x_4134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_3898_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_3898_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4140_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169);
v___x_4141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170));
v___x_4142_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4141_, v_currMacroScope_3877_);
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174));
v___x_4144_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4144_, 0, v___x_3898_);
lean_ctor_set(v___x_4144_, 1, v___x_4140_);
lean_ctor_set(v___x_4144_, 2, v___x_4142_);
lean_ctor_set(v___x_4144_, 3, v___x_4143_);
v___x_4145_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4144_);
lean_inc_ref_n(v___x_4138_, 2);
v___x_4146_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4136_, v___x_4138_, v___x_4145_);
v___x_4147_ = l_Lean_Syntax_node3(v___x_3898_, v___x_4088_, v___x_4097_, v___x_4146_, v___x_3935_);
v___x_4148_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176);
v___x_4149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177));
v___x_4150_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4149_, v_currMacroScope_3877_);
v___x_4151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4151_, 0, v___x_3898_);
lean_ctor_set(v___x_4151_, 1, v___x_4148_);
lean_ctor_set(v___x_4151_, 2, v___x_4150_);
lean_ctor_set(v___x_4151_, 3, v___x_3915_);
v___x_4152_ = l_Lean_Syntax_node3(v___x_3898_, v___x_4135_, v___x_4147_, v___x_3965_, v___x_4151_);
lean_inc_n(v___x_3975_, 3);
v___x_4153_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_3975_);
v___x_4154_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4152_, v___x_4153_);
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179));
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180));
v___x_4157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_3898_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182));
v___x_4159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183));
v___x_4160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_3898_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185));
v___x_4162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187));
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188));
v___x_4164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_3898_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4162_, v___x_4164_);
v___x_4166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189));
v___x_4167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_3898_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4162_, v___x_4167_);
lean_inc(v___x_4168_);
v___x_4169_ = l_Lean_Syntax_node3(v___x_3898_, v___x_4161_, v___x_4165_, v___x_3975_, v___x_4168_);
lean_inc_ref_n(v___x_4160_, 2);
v___x_4170_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4158_, v___x_4160_, v___x_4169_);
lean_inc_ref_n(v___x_4157_, 2);
v___x_4171_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4155_, v___x_4157_, v___x_4170_);
v___x_4172_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4171_);
v___x_4173_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4172_, v___x_3901_);
v___x_4174_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4173_);
v___x_4175_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4174_);
lean_inc_ref_n(v___x_4047_, 2);
v___x_4176_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4132_, v___x_4134_, v___x_4154_, v___x_4047_, v___x_4175_);
v___x_4177_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4176_, v___x_3901_);
v___x_4178_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191);
v___x_4179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192));
v___x_4180_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4179_, v_currMacroScope_3877_);
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197));
v___x_4182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4182_, 0, v___x_3898_);
lean_ctor_set(v___x_4182_, 1, v___x_4178_);
lean_ctor_set(v___x_4182_, 2, v___x_4180_);
lean_ctor_set(v___x_4182_, 3, v___x_4181_);
v___x_4183_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199);
v___x_4184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200));
v___x_4185_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4184_, v_currMacroScope_3877_);
v___x_4186_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4186_, 0, v___x_3898_);
lean_ctor_set(v___x_4186_, 1, v___x_4183_);
lean_ctor_set(v___x_4186_, 2, v___x_4185_);
lean_ctor_set(v___x_4186_, 3, v___x_3915_);
v___x_4187_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201);
v___x_4188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202));
v___x_4189_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4188_, v_currMacroScope_3877_);
v___x_4190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204));
v___x_4191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4191_, 0, v___x_3898_);
lean_ctor_set(v___x_4191_, 1, v___x_4187_);
lean_ctor_set(v___x_4191_, 2, v___x_4189_);
lean_ctor_set(v___x_4191_, 3, v___x_4190_);
v___x_4192_ = l_Lean_Syntax_node5(v___x_3898_, v___x_3958_, v___x_3921_, v___x_4186_, v___x_3952_, v___x_4191_, v___x_3935_);
v___x_4193_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_4192_, v___x_3975_);
v___x_4194_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4182_, v___x_4193_);
v___x_4195_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4194_);
v___x_4196_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4195_, v___x_3901_);
v___x_4197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206));
v___x_4198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208));
v___x_4199_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210);
v___x_4200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211));
v___x_4201_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4200_, v_currMacroScope_3877_);
v___x_4202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4202_, 0, v___x_3898_);
lean_ctor_set(v___x_4202_, 1, v___x_4199_);
lean_ctor_set(v___x_4202_, 2, v___x_4201_);
lean_ctor_set(v___x_4202_, 3, v___x_3915_);
v___x_4203_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213);
v___x_4204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214));
v___x_4205_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4204_, v_currMacroScope_3877_);
v___x_4206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219));
v___x_4207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4207_, 0, v___x_3898_);
lean_ctor_set(v___x_4207_, 1, v___x_4203_);
lean_ctor_set(v___x_4207_, 2, v___x_4205_);
lean_ctor_set(v___x_4207_, 3, v___x_4206_);
v___x_4208_ = l_Lean_Syntax_node3(v___x_3898_, v___x_3885_, v___x_4061_, v___x_3975_, v___x_4081_);
v___x_4209_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4207_, v___x_4208_);
v___x_4210_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4209_);
lean_inc_ref(v___x_4202_);
v___x_4211_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4198_, v___x_4202_, v___x_3901_, v___x_4138_, v___x_4210_);
v___x_4212_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4197_, v___x_4052_, v___x_3901_, v___x_4054_, v___x_4211_);
v___x_4213_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4212_, v___x_3901_);
v___x_4214_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221);
v___x_4215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223));
v___x_4216_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4215_, v_currMacroScope_3877_);
v___x_4217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4217_, 0, v___x_3898_);
lean_ctor_set(v___x_4217_, 1, v___x_4214_);
lean_ctor_set(v___x_4217_, 2, v___x_4216_);
lean_ctor_set(v___x_4217_, 3, v___x_3915_);
v___x_4218_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4114_, v___x_3901_, v___x_4217_);
v___x_4219_ = l_Lean_Syntax_node6(v___x_3898_, v___x_4111_, v___x_4113_, v___x_4218_, v___x_4121_, v___x_4129_, v___x_3901_, v___x_3901_);
v___x_4220_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4219_, v___x_3901_);
v___x_4221_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225);
v___x_4222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227));
v___x_4223_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4222_, v_currMacroScope_3877_);
v___x_4224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4224_, 0, v___x_3898_);
lean_ctor_set(v___x_4224_, 1, v___x_4221_);
lean_ctor_set(v___x_4224_, 2, v___x_4223_);
lean_ctor_set(v___x_4224_, 3, v___x_3915_);
v___x_4225_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4114_, v___x_3901_, v___x_4224_);
v___x_4226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228));
v___x_4227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_3898_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
v___x_4228_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4162_, v___x_4227_);
v___x_4229_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4161_, v___x_4228_);
v___x_4230_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4158_, v___x_4160_, v___x_4229_);
v___x_4231_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4155_, v___x_4157_, v___x_4230_);
v___x_4232_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4231_);
v___x_4233_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4232_, v___x_3901_);
v___x_4234_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4233_);
v___x_4235_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4234_);
v___x_4236_ = l_Lean_Syntax_node6(v___x_3898_, v___x_4111_, v___x_4113_, v___x_4225_, v___x_4121_, v___x_4235_, v___x_3901_, v___x_3901_);
v___x_4237_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4236_, v___x_3901_);
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230));
v___x_4239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231));
v___x_4240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_3898_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233);
v___x_4242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234));
v___x_4243_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4242_, v_currMacroScope_3877_);
v___x_4244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4244_, 0, v___x_3898_);
lean_ctor_set(v___x_4244_, 1, v___x_4241_);
lean_ctor_set(v___x_4244_, 2, v___x_4243_);
lean_ctor_set(v___x_4244_, 3, v___x_3915_);
v___x_4245_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4202_);
lean_inc(v___x_4245_);
v___x_4246_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4009_, v___x_4245_);
v___x_4247_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4246_);
lean_inc_ref(v___x_4244_);
v___x_4248_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4198_, v___x_4244_, v___x_3901_, v___x_4138_, v___x_4247_);
v___x_4249_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4197_, v___x_4052_, v___x_3901_, v___x_4054_, v___x_4248_);
v___x_4250_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4249_, v___x_3901_);
v___x_4251_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4244_);
v___x_4252_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4122_, v___x_4124_, v___x_4251_);
v___x_4253_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4252_, v___x_3901_);
v___x_4254_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_4250_, v___x_4253_);
v___x_4255_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4254_);
v___x_4256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236));
v___x_4257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237));
v___x_4258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_3898_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239);
v___x_4260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240));
v___x_4261_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4260_, v_currMacroScope_3877_);
v___x_4262_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4262_, 0, v___x_3898_);
lean_ctor_set(v___x_4262_, 1, v___x_4259_);
lean_ctor_set(v___x_4262_, 2, v___x_4261_);
lean_ctor_set(v___x_4262_, 3, v___x_3915_);
v___x_4263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241));
v___x_4264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_3898_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243);
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244));
v___x_4267_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4266_, v_currMacroScope_3877_);
v___x_4268_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4268_, 0, v___x_3898_);
lean_ctor_set(v___x_4268_, 1, v___x_4265_);
lean_ctor_set(v___x_4268_, 2, v___x_4267_);
lean_ctor_set(v___x_4268_, 3, v___x_3915_);
lean_inc_ref_n(v___x_4268_, 2);
v___x_4269_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4057_, v___x_4268_);
v___x_4270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245));
v___x_4271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_3898_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4162_, v___x_4271_);
v___x_4273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247);
v___x_4274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248));
v___x_4275_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4274_, v_currMacroScope_3877_);
v___x_4276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251));
v___x_4277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4277_, 0, v___x_3898_);
lean_ctor_set(v___x_4277_, 1, v___x_4273_);
lean_ctor_set(v___x_4277_, 2, v___x_4275_);
lean_ctor_set(v___x_4277_, 3, v___x_4276_);
v___x_4278_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4277_, v___x_4245_);
v___x_4279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252));
v___x_4280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_3898_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4162_, v___x_4280_);
v___x_4282_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254);
v___x_4283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256));
v___x_4284_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4283_, v_currMacroScope_3877_);
v___x_4285_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4285_, 0, v___x_3898_);
lean_ctor_set(v___x_4285_, 1, v___x_4282_);
lean_ctor_set(v___x_4285_, 2, v___x_4284_);
lean_ctor_set(v___x_4285_, 3, v___x_3915_);
v___x_4286_ = l_Lean_Syntax_node5(v___x_3898_, v___x_4161_, v___x_4272_, v___x_4278_, v___x_4281_, v___x_4285_, v___x_4168_);
v___x_4287_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4158_, v___x_4160_, v___x_4286_);
v___x_4288_ = l_Lean_Syntax_node5(v___x_3898_, v___x_4056_, v___x_4269_, v___x_3901_, v___x_3901_, v___x_3952_, v___x_4287_);
v___x_4289_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4055_, v___x_4288_);
v___x_4290_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4050_, v___x_4052_, v___x_3901_, v___x_4054_, v___x_4289_);
v___x_4291_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4290_, v___x_3901_);
v___x_4292_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257);
v___x_4293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258));
v___x_4294_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4293_, v_currMacroScope_3877_);
v___x_4295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260));
v___x_4296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4296_, 0, v___x_3898_);
lean_ctor_set(v___x_4296_, 1, v___x_4292_);
lean_ctor_set(v___x_4296_, 2, v___x_4294_);
lean_ctor_set(v___x_4296_, 3, v___x_4295_);
v___x_4297_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4114_, v___x_3901_, v___x_4296_);
v___x_4298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262);
v___x_4299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263));
v___x_4300_ = l_Lean_addMacroScope(v_quotContext_3876_, v___x_4299_, v_currMacroScope_3877_);
v___x_4301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266));
v___x_4302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4302_, 0, v___x_3898_);
lean_ctor_set(v___x_4302_, 1, v___x_4298_);
lean_ctor_set(v___x_4302_, 2, v___x_4300_);
lean_ctor_set(v___x_4302_, 3, v___x_4301_);
v___x_4303_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4268_);
v___x_4304_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4302_, v___x_4303_);
v___x_4305_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4304_);
v___x_4306_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4305_, v___x_3901_);
v___x_4307_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_4306_, v___x_4127_);
v___x_4308_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4307_);
v___x_4309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267));
v___x_4310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_3898_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4155_, v___x_4157_, v___x_4268_);
v___x_4312_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4311_);
v___x_4313_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4312_, v___x_3901_);
v___x_4314_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4314_);
v___x_4316_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_4310_, v___x_4315_);
v___x_4317_ = l_Lean_Syntax_node6(v___x_3898_, v___x_4111_, v___x_4113_, v___x_4297_, v___x_4121_, v___x_4308_, v___x_3901_, v___x_4316_);
v___x_4318_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4317_, v___x_3901_);
v___x_4319_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_4291_, v___x_4318_);
v___x_4320_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4319_);
v___x_4321_ = l_Lean_Syntax_node5(v___x_3898_, v___x_4256_, v___x_4258_, v___x_4262_, v___x_3901_, v___x_4264_, v___x_4320_);
v___x_4322_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4321_);
v___x_4323_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4238_, v___x_4240_, v___x_4255_, v___x_4322_, v___x_3901_);
v___x_4324_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4323_, v___x_3901_);
v___x_4325_ = l_Lean_Syntax_node8(v___x_3898_, v___x_3885_, v___x_4110_, v___x_4131_, v___x_4177_, v___x_4196_, v___x_4213_, v___x_4220_, v___x_4237_, v___x_4324_);
v___x_4326_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4325_);
v___x_4327_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4046_, v___x_4047_, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3885_, v___x_4031_, v___x_4327_);
v___x_4329_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v___x_4077_, v___x_4328_);
v___x_4330_ = l_Lean_Syntax_node5(v___x_3898_, v___x_4056_, v___x_4072_, v___x_3901_, v___x_3948_, v___x_3952_, v___x_4329_);
v___x_4331_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4055_, v___x_4330_);
v___x_4332_ = l_Lean_Syntax_node4(v___x_3898_, v___x_4050_, v___x_4052_, v___x_3901_, v___x_4054_, v___x_4331_);
v___x_4333_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4332_, v___x_3901_);
v___x_4334_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4139_, v___x_4071_);
v___x_4335_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4049_, v___x_4334_, v___x_3901_);
v___x_4336_ = l_Lean_Syntax_node3(v___x_3898_, v___x_3885_, v___x_4066_, v___x_4333_, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_node1(v___x_3898_, v___x_4048_, v___x_4336_);
v___x_4338_ = l_Lean_Syntax_node2(v___x_3898_, v___x_4046_, v___x_4047_, v___x_4337_);
v___x_4339_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3885_, v___x_4338_);
v___x_4340_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3939_, v_adapt_3872_, v___x_4339_);
v___x_4341_ = l_Lean_Syntax_node4(v___x_3898_, v___x_3950_, v___x_3952_, v___x_4340_, v___x_3979_, v___x_3901_);
v___x_4342_ = l_Lean_Syntax_node5(v___x_3898_, v___x_3908_, v___x_3910_, v___x_4026_, v___x_4044_, v___x_4341_, v___x_3901_);
v___x_4343_ = l_Lean_Syntax_node2(v___x_3898_, v___x_3899_, v___x_4019_, v___x_4342_);
v___x_4344_ = l_Lean_Syntax_node3(v___x_3898_, v___x_3885_, v___x_3982_, v___x_4014_, v___x_4343_);
v___x_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v_a_3875_);
return v___x_4345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___boxed(lean_object* v_doc_x3f_4349_, lean_object* v_elabName_4350_, lean_object* v_type_4351_, lean_object* v_monadName_4352_, lean_object* v_adapt_4353_, lean_object* v_recover_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v_doc_x3f_4349_, v_elabName_4350_, v_type_4351_, v_monadName_4352_, v_adapt_4353_, v_recover_4354_, v_a_4355_, v_a_4356_);
lean_dec_ref(v_a_4355_);
return v_res_4357_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1(void){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0));
v___x_4402_ = l_String_toRawSubstring_x27(v___x_4401_);
return v___x_4402_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8));
v___x_4422_ = l_Lean_mkCIdent(v___x_4421_);
return v___x_4422_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12(void){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11));
v___x_4427_ = l_Lean_mkCIdent(v___x_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(lean_object* v_x_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4431_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
lean_inc(v_x_4428_);
v___x_4432_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
lean_dec(v_x_4428_);
v___x_4433_ = lean_box(1);
v___x_4434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
lean_ctor_set(v___x_4434_, 1, v_a_4430_);
return v___x_4434_;
}
else
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v_elabName_4438_; lean_object* v___x_4439_; lean_object* v_type_4440_; lean_object* v___y_4442_; lean_object* v___x_4495_; 
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = l_Lean_Syntax_getArg(v_x_4428_, v___x_4435_);
v___x_4437_ = lean_unsigned_to_nat(2u);
v_elabName_4438_ = l_Lean_Syntax_getArg(v_x_4428_, v___x_4437_);
v___x_4439_ = lean_unsigned_to_nat(3u);
v_type_4440_ = l_Lean_Syntax_getArg(v_x_4428_, v___x_4439_);
lean_dec(v_x_4428_);
v___x_4495_ = l_Lean_Syntax_getOptional_x3f(v___x_4436_);
lean_dec(v___x_4436_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_box(0);
v___y_4442_ = v___x_4496_;
goto v___jp_4441_;
}
else
{
lean_object* v_val_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
v_val_4497_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4495_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_val_4497_);
lean_dec(v___x_4495_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_val_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
v___y_4442_ = v___x_4502_;
goto v___jp_4441_;
}
}
}
v___jp_4441_:
{
lean_object* v_quotContext_4443_; lean_object* v_currMacroScope_4444_; lean_object* v_ref_4445_; uint8_t v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v_a_4486_; lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
v_quotContext_4443_ = lean_ctor_get(v_a_4429_, 1);
v_currMacroScope_4444_ = lean_ctor_get(v_a_4429_, 2);
v_ref_4445_ = lean_ctor_get(v_a_4429_, 5);
v___x_4446_ = 0;
v___x_4447_ = l_Lean_SourceInfo_fromRef(v_ref_4445_, v___x_4446_);
v___x_4448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_4447_, 12);
v___x_4452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4447_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
v___x_4453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4455_ = lean_box(0);
lean_inc_n(v_currMacroScope_4444_, 3);
lean_inc_n(v_quotContext_4443_, 3);
v___x_4456_ = l_Lean_addMacroScope(v_quotContext_4443_, v___x_4455_, v_currMacroScope_4444_);
v___x_4457_ = lean_box(0);
v___x_4458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4459_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4447_);
lean_ctor_set(v___x_4459_, 1, v___x_4454_);
lean_ctor_set(v___x_4459_, 2, v___x_4456_);
lean_ctor_set(v___x_4459_, 3, v___x_4458_);
v___x_4460_ = l_Lean_Syntax_node1(v___x_4447_, v___x_4453_, v___x_4459_);
v___x_4461_ = l_Lean_Syntax_node2(v___x_4447_, v___x_4450_, v___x_4452_, v___x_4460_);
v___x_4462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4447_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4466_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1);
v___x_4467_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2));
v___x_4468_ = l_Lean_addMacroScope(v_quotContext_4443_, v___x_4467_, v_currMacroScope_4444_);
v___x_4469_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6));
v___x_4470_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4447_);
lean_ctor_set(v___x_4470_, 1, v___x_4466_);
lean_ctor_set(v___x_4470_, 2, v___x_4468_);
lean_ctor_set(v___x_4470_, 3, v___x_4469_);
v___x_4471_ = l_Lean_Syntax_node1(v___x_4447_, v___x_4465_, v___x_4470_);
v___x_4472_ = l_Lean_Syntax_node2(v___x_4447_, v___x_4462_, v___x_4464_, v___x_4471_);
v___x_4473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_4474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4447_);
lean_ctor_set(v___x_4474_, 1, v___x_4473_);
v___x_4475_ = l_Lean_Syntax_node3(v___x_4447_, v___x_4449_, v___x_4461_, v___x_4472_, v___x_4474_);
v___x_4476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_4477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4447_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
v___x_4478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4480_ = l_Lean_addMacroScope(v_quotContext_4443_, v___x_4479_, v_currMacroScope_4444_);
v___x_4481_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4447_);
lean_ctor_set(v___x_4481_, 1, v___x_4478_);
lean_ctor_set(v___x_4481_, 2, v___x_4480_);
lean_ctor_set(v___x_4481_, 3, v___x_4457_);
v___x_4482_ = l_Lean_Syntax_node3(v___x_4447_, v___x_4448_, v___x_4475_, v___x_4477_, v___x_4481_);
v___x_4483_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9);
v___x_4484_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12);
v___x_4485_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4442_, v_elabName_4438_, v_type_4440_, v___x_4483_, v___x_4484_, v___x_4482_, v_a_4429_, v_a_4430_);
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
v_a_4487_ = lean_ctor_get(v___x_4485_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4485_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_inc(v_a_4486_);
lean_dec(v___x_4485_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4486_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___boxed(lean_object* v_x_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(v_x_4505_, v_a_4506_, v_a_4507_);
lean_dec_ref(v_a_4506_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4515_ = lean_unsigned_to_nat(2u);
v___x_4516_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4514_, v___x_4515_, v_a_4510_, v_a_4511_, v_a_4512_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed(lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
return v_res_4521_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed), 4, 0);
v___x_4523_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1(){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
v___x_4526_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0);
v___x_4527_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4525_, v___x_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___boxed(lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
return v_res_4529_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1));
v___x_4563_ = l_Lean_mkCIdent(v___x_4562_);
return v___x_4563_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4));
v___x_4571_ = l_Lean_mkCIdent(v___x_4570_);
return v___x_4571_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18));
v___x_4573_ = l_Lean_mkCIdent(v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(lean_object* v_x_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
lean_inc(v_x_4574_);
v___x_4578_ = l_Lean_Syntax_isOfKind(v_x_4574_, v___x_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
lean_dec(v_x_4574_);
v___x_4579_ = lean_box(1);
v___x_4580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v_a_4576_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v_elabName_4584_; lean_object* v___x_4585_; lean_object* v_type_4586_; lean_object* v___y_4588_; lean_object* v___x_4602_; 
v___x_4581_ = lean_unsigned_to_nat(0u);
v___x_4582_ = l_Lean_Syntax_getArg(v_x_4574_, v___x_4581_);
v___x_4583_ = lean_unsigned_to_nat(2u);
v_elabName_4584_ = l_Lean_Syntax_getArg(v_x_4574_, v___x_4583_);
v___x_4585_ = lean_unsigned_to_nat(3u);
v_type_4586_ = l_Lean_Syntax_getArg(v_x_4574_, v___x_4585_);
lean_dec(v_x_4574_);
v___x_4602_ = l_Lean_Syntax_getOptional_x3f(v___x_4582_);
lean_dec(v___x_4582_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_box(0);
v___y_4588_ = v___x_4603_;
goto v___jp_4587_;
}
else
{
lean_object* v_val_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
v_val_4604_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4602_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_val_4604_);
lean_dec(v___x_4602_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_val_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
v___y_4588_ = v___x_4609_;
goto v___jp_4587_;
}
}
}
v___jp_4587_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v_a_4593_; lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
v___x_4589_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2);
v___x_4590_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5);
v___x_4591_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6);
v___x_4592_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4588_, v_elabName_4584_, v_type_4586_, v___x_4589_, v___x_4590_, v___x_4591_, v_a_4575_, v_a_4576_);
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
v_a_4594_ = lean_ctor_get(v___x_4592_, 1);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4592_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_inc(v_a_4593_);
lean_dec(v___x_4592_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4593_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___boxed(lean_object* v_x_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(v_x_4612_, v_a_4613_, v_a_4614_);
lean_dec_ref(v_a_4613_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4621_ = lean_unsigned_to_nat(2u);
v___x_4622_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4620_, v___x_4621_, v_a_4616_, v_a_4617_, v_a_4618_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed(lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(v_a_4623_, v_a_4624_, v_a_4625_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
return v_res_4627_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed), 4, 0);
v___x_4629_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4629_, 0, v___x_4628_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
v___x_4632_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0);
v___x_4633_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4631_, v___x_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___boxed(lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
return v_res_4635_;
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
