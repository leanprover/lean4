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
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Option is not boolean-valued, so `("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " := ...)` syntax must be used"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9;
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
lean_object* v___x_134_; lean_object* v_env_135_; lean_object* v___x_136_; lean_object* v_mctx_137_; lean_object* v_lctx_138_; lean_object* v_options_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_134_);
v___x_136_ = lean_st_ref_get(v___y_130_);
v_mctx_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_mctx_137_);
lean_dec(v___x_136_);
v_lctx_138_ = lean_ctor_get(v___y_129_, 2);
v_options_139_ = lean_ctor_get(v___y_131_, 2);
lean_inc_ref(v_options_139_);
lean_inc_ref(v_lctx_138_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_135_);
lean_ctor_set(v___x_140_, 1, v_mctx_137_);
lean_ctor_set(v___x_140_, 2, v_lctx_138_);
lean_ctor_set(v___x_140_, 3, v_options_139_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_128_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2___boxed(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msgData_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_ref_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_ref_156_ = lean_ctor_get(v___y_153_, 5);
v___x_157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc(v_ref_156_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v_ref_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg___boxed(lean_object* v_msg_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__2));
v___x_178_ = lean_unsigned_to_nat(14u);
v___x_179_ = lean_unsigned_to_nat(22u);
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__1));
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__0));
v___x_182_ = l_mkPanicMessageWithDecl(v___x_181_, v___x_180_, v___x_179_, v___x_178_, v___x_177_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__4));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__6));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__8));
v___x_191_ = l_Lean_stringToMessageData(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__10));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__14));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(lean_object* v_structName_201_, lean_object* v_fieldName_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___x_214_; lean_object* v_env_215_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; uint8_t v___x_249_; 
v___x_214_ = lean_st_ref_get(v_a_206_);
v_env_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref_n(v_env_215_, 2);
lean_dec(v___x_214_);
lean_inc(v_structName_201_);
v___x_249_ = l_Lean_isStructure(v_env_215_, v_structName_201_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_env_215_);
lean_dec(v_fieldName_202_);
v___x_250_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_251_ = l_Lean_MessageData_ofConstName(v_structName_201_, v___x_249_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_254_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
v___y_217_ = v_a_203_;
v___y_218_ = v_a_204_;
v___y_219_ = v_a_205_;
v___y_220_ = v_a_206_;
goto v___jp_216_;
}
v___jp_208_:
{
lean_object* v_projFn_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_projFn_211_ = lean_ctor_get(v___y_210_, 1);
lean_inc(v_projFn_211_);
lean_dec_ref(v___y_210_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___y_209_);
lean_ctor_set(v___x_212_, 1, v_projFn_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
v___jp_216_:
{
lean_object* v___x_221_; 
lean_inc(v_structName_201_);
lean_inc_ref(v_env_215_);
v___x_221_ = l_Lean_findField_x3f(v_env_215_, v_structName_201_, v_fieldName_202_);
if (lean_obj_tag(v___x_221_) == 1)
{
lean_object* v_val_222_; lean_object* v___x_223_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
lean_inc_ref(v_env_215_);
v___x_223_ = l_Lean_getPathToBaseStructure_x3f(v_env_215_, v_val_222_, v_structName_201_);
if (lean_obj_tag(v___x_223_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = lean_box(0);
v___x_226_ = l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0(v___x_225_, v_val_224_);
lean_dec(v_val_224_);
lean_inc(v_fieldName_202_);
v___x_227_ = l_Lean_Name_append(v___x_226_, v_fieldName_202_);
v___x_228_ = l_Lean_getFieldInfo_x3f(v_env_215_, v_val_222_, v_fieldName_202_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3);
v___x_230_ = l_panic___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__1(v___x_229_);
v___y_209_ = v___x_227_;
v___y_210_ = v___x_230_;
goto v___jp_208_;
}
else
{
lean_object* v_val_231_; 
v_val_231_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_228_, 1);
v___y_209_ = v___x_227_;
v___y_210_ = v_val_231_;
goto v___jp_208_;
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___x_223_);
lean_dec(v_val_222_);
lean_dec_ref(v_env_215_);
v___x_232_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5);
v___x_233_ = l_Lean_MessageData_ofName(v_fieldName_202_);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_236_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_237_;
}
}
else
{
lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_221_);
lean_dec_ref(v_env_215_);
v___x_238_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9);
v___x_239_ = 0;
v___x_240_ = l_Lean_MessageData_ofConstName(v_structName_201_, v___x_239_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_MessageData_ofName(v_fieldName_202_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_247_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___boxed(lean_object* v_structName_264_, lean_object* v_fieldName_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_264_, v_fieldName_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(lean_object* v_00_u03b1_272_, lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___boxed(lean_object* v_00_u03b1_280_, lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(v_00_u03b1_280_, v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__0));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__2));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(lean_object* v_fst_294_, lean_object* v_structName_295_, lean_object* v_00_u03b1_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1);
v___x_303_ = l_Lean_MessageData_ofName(v_fst_294_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = 0;
v___x_308_ = l_Lean_MessageData_ofConstName(v_structName_295_, v___x_307_);
v___x_309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_306_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_311_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___boxed(lean_object* v_fst_313_, lean_object* v_structName_314_, lean_object* v_00_u03b1_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_313_, v_structName_314_, v_00_u03b1_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_322_, lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_fileName_329_; lean_object* v_fileMap_330_; lean_object* v_options_331_; lean_object* v_currRecDepth_332_; lean_object* v_maxRecDepth_333_; lean_object* v_ref_334_; lean_object* v_currNamespace_335_; lean_object* v_openDecls_336_; lean_object* v_initHeartbeats_337_; lean_object* v_maxHeartbeats_338_; lean_object* v_quotContext_339_; lean_object* v_currMacroScope_340_; uint8_t v_diag_341_; lean_object* v_cancelTk_x3f_342_; uint8_t v_suppressElabErrors_343_; lean_object* v_inheritedTraceOptions_344_; lean_object* v_ref_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_fileName_329_ = lean_ctor_get(v___y_326_, 0);
v_fileMap_330_ = lean_ctor_get(v___y_326_, 1);
v_options_331_ = lean_ctor_get(v___y_326_, 2);
v_currRecDepth_332_ = lean_ctor_get(v___y_326_, 3);
v_maxRecDepth_333_ = lean_ctor_get(v___y_326_, 4);
v_ref_334_ = lean_ctor_get(v___y_326_, 5);
v_currNamespace_335_ = lean_ctor_get(v___y_326_, 6);
v_openDecls_336_ = lean_ctor_get(v___y_326_, 7);
v_initHeartbeats_337_ = lean_ctor_get(v___y_326_, 8);
v_maxHeartbeats_338_ = lean_ctor_get(v___y_326_, 9);
v_quotContext_339_ = lean_ctor_get(v___y_326_, 10);
v_currMacroScope_340_ = lean_ctor_get(v___y_326_, 11);
v_diag_341_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*14);
v_cancelTk_x3f_342_ = lean_ctor_get(v___y_326_, 12);
v_suppressElabErrors_343_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_344_ = lean_ctor_get(v___y_326_, 13);
v_ref_345_ = l_Lean_replaceRef(v_ref_322_, v_ref_334_);
lean_inc_ref(v_inheritedTraceOptions_344_);
lean_inc(v_cancelTk_x3f_342_);
lean_inc(v_currMacroScope_340_);
lean_inc(v_quotContext_339_);
lean_inc(v_maxHeartbeats_338_);
lean_inc(v_initHeartbeats_337_);
lean_inc(v_openDecls_336_);
lean_inc(v_currNamespace_335_);
lean_inc(v_maxRecDepth_333_);
lean_inc(v_currRecDepth_332_);
lean_inc_ref(v_options_331_);
lean_inc_ref(v_fileMap_330_);
lean_inc_ref(v_fileName_329_);
v___x_346_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_346_, 0, v_fileName_329_);
lean_ctor_set(v___x_346_, 1, v_fileMap_330_);
lean_ctor_set(v___x_346_, 2, v_options_331_);
lean_ctor_set(v___x_346_, 3, v_currRecDepth_332_);
lean_ctor_set(v___x_346_, 4, v_maxRecDepth_333_);
lean_ctor_set(v___x_346_, 5, v_ref_345_);
lean_ctor_set(v___x_346_, 6, v_currNamespace_335_);
lean_ctor_set(v___x_346_, 7, v_openDecls_336_);
lean_ctor_set(v___x_346_, 8, v_initHeartbeats_337_);
lean_ctor_set(v___x_346_, 9, v_maxHeartbeats_338_);
lean_ctor_set(v___x_346_, 10, v_quotContext_339_);
lean_ctor_set(v___x_346_, 11, v_currMacroScope_340_);
lean_ctor_set(v___x_346_, 12, v_cancelTk_x3f_342_);
lean_ctor_set(v___x_346_, 13, v_inheritedTraceOptions_344_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*14, v_diag_341_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*14 + 1, v_suppressElabErrors_343_);
v___x_347_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_323_, v___y_324_, v___y_325_, v___x_346_, v___y_327_);
lean_dec_ref_known(v___x_346_, 14);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_348_, v_msg_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v_ref_348_);
return v_res_355_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_ctor_set(v___x_361_, 2, v___x_360_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
lean_ctor_set(v___x_361_, 4, v___x_359_);
lean_ctor_set(v___x_361_, 5, v___x_359_);
lean_ctor_set(v___x_361_, 6, v___x_359_);
lean_ctor_set(v___x_361_, 7, v___x_359_);
lean_ctor_set(v___x_361_, 8, v___x_359_);
lean_ctor_set(v___x_361_, 9, v___x_359_);
lean_ctor_set(v___x_361_, 10, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(32u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = ((size_t)5ULL);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_unsigned_to_nat(32u);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_370_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
lean_ctor_set(v___x_370_, 2, v___x_366_);
lean_ctor_set(v___x_370_, 3, v___x_366_);
lean_ctor_set_usize(v___x_370_, 4, v___x_365_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_371_ = lean_box(1);
v___x_372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
lean_ctor_set(v___x_374_, 2, v___x_371_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_396_, lean_object* v_declHint_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_env_401_; uint8_t v___x_402_; 
v___x_400_ = lean_st_ref_get(v___y_398_);
v_env_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_400_);
v___x_402_ = l_Lean_Name_isAnonymous(v_declHint_397_);
if (v___x_402_ == 0)
{
uint8_t v_isExporting_403_; 
v_isExporting_403_ = lean_ctor_get_uint8(v_env_401_, sizeof(void*)*8);
if (v_isExporting_403_ == 0)
{
lean_object* v___x_404_; 
lean_dec_ref(v_env_401_);
lean_dec(v_declHint_397_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_msg_396_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; uint8_t v___x_406_; 
lean_inc_ref(v_env_401_);
v___x_405_ = l_Lean_Environment_setExporting(v_env_401_, v___x_402_);
lean_inc(v_declHint_397_);
lean_inc_ref(v___x_405_);
v___x_406_ = l_Lean_Environment_contains(v___x_405_, v_declHint_397_, v_isExporting_403_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
lean_dec_ref(v___x_405_);
lean_dec_ref(v_env_401_);
lean_dec(v_declHint_397_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_msg_396_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_c_413_; lean_object* v___x_414_; 
v___x_408_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_410_ = l_Lean_Options_empty;
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v___x_405_);
lean_ctor_set(v___x_411_, 1, v___x_408_);
lean_ctor_set(v___x_411_, 2, v___x_409_);
lean_ctor_set(v___x_411_, 3, v___x_410_);
lean_inc(v_declHint_397_);
v___x_412_ = l_Lean_MessageData_ofConstName(v_declHint_397_, v___x_402_);
v_c_413_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_413_, 0, v___x_411_);
lean_ctor_set(v_c_413_, 1, v___x_412_);
v___x_414_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_401_, v_declHint_397_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_env_401_);
lean_dec(v_declHint_397_);
v___x_415_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_c_413_);
v___x_417_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Lean_MessageData_note(v___x_418_);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v_msg_396_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_457_; 
v_val_422_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_457_ == 0)
{
v___x_424_ = v___x_414_;
v_isShared_425_ = v_isSharedCheck_457_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_dec(v___x_414_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_457_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_mod_429_; uint8_t v___x_430_; 
v___x_426_ = lean_box(0);
v___x_427_ = l_Lean_Environment_header(v_env_401_);
lean_dec_ref(v_env_401_);
v___x_428_ = l_Lean_EnvironmentHeader_moduleNames(v___x_427_);
v_mod_429_ = lean_array_get(v___x_426_, v___x_428_, v_val_422_);
lean_dec(v_val_422_);
lean_dec_ref(v___x_428_);
v___x_430_ = l_Lean_isPrivateName(v_declHint_397_);
lean_dec(v_declHint_397_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_c_413_);
v___x_433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_MessageData_ofName(v_mod_429_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = l_Lean_MessageData_note(v___x_438_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v_msg_396_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v___x_440_);
v___x_442_ = v___x_424_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_c_413_);
v___x_446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_MessageData_ofName(v_mod_429_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_Lean_MessageData_note(v___x_451_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v_msg_396_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v___x_453_);
v___x_455_ = v___x_424_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v_env_401_);
lean_dec(v_declHint_397_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_msg_396_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_459_, lean_object* v_declHint_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_459_, v_declHint_460_, v___y_461_);
lean_dec(v___y_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_464_, lean_object* v_declHint_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v___x_471_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_464_, v_declHint_465_, v___y_469_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = l_Lean_unknownIdentifierMessageTag;
v___x_477_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_a_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_482_, lean_object* v_declHint_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_482_, v_declHint_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_490_, lean_object* v_msg_491_, lean_object* v_declHint_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_500_; 
v___x_498_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_491_, v_declHint_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_490_, v_a_499_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_501_, lean_object* v_msg_502_, lean_object* v_declHint_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_501_, v_msg_502_, v_declHint_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v_ref_501_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_513_, lean_object* v_constName_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_520_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_521_ = 0;
lean_inc(v_constName_514_);
v___x_522_ = l_Lean_MessageData_ofConstName(v_constName_514_, v___x_521_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_513_, v___x_525_, v_constName_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_527_, lean_object* v_constName_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_527_, v_constName_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v_ref_527_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(lean_object* v_constName_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_ref_541_; lean_object* v___x_542_; 
v_ref_541_ = lean_ctor_get(v___y_538_, 5);
v___x_542_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_541_, v_constName_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg___boxed(lean_object* v_constName_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(lean_object* v_constName_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; lean_object* v_env_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
v___x_556_ = lean_st_ref_get(v___y_554_);
v_env_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc_ref(v_env_557_);
lean_dec(v___x_556_);
v___x_558_ = 0;
lean_inc(v_constName_550_);
v___x_559_ = l_Lean_Environment_find_x3f(v_env_557_, v_constName_550_, v___x_558_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_560_;
}
else
{
lean_object* v_val_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_constName_550_);
v_val_561_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_559_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_val_561_);
lean_dec(v___x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 0);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_val_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0___boxed(lean_object* v_constName_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_constName_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(lean_object* v_structName_579_, lean_object* v_field_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
if (lean_obj_tag(v_field_580_) == 1)
{
lean_object* v_pre_586_; 
v_pre_586_ = lean_ctor_get(v_field_580_, 0);
if (lean_obj_tag(v_pre_586_) == 0)
{
lean_object* v_str_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_str_587_ = lean_ctor_get(v_field_580_, 1);
lean_inc_ref(v_str_587_);
lean_dec_ref_known(v_field_580_, 2);
v___x_588_ = lean_box(0);
v___x_589_ = l_Lean_Name_str___override(v___x_588_, v_str_587_);
v___x_590_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_579_, v___x_589_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_590_;
}
else
{
lean_object* v_str_591_; lean_object* v___x_592_; 
lean_inc(v_pre_586_);
v_str_591_ = lean_ctor_get(v_field_580_, 1);
lean_inc_ref(v_str_591_);
lean_dec_ref_known(v_field_580_, 2);
lean_inc(v_structName_579_);
v___x_592_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_579_, v_pre_586_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v_fst_594_ = lean_ctor_get(v_a_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v_a_593_, 1);
lean_inc(v_snd_595_);
lean_dec(v_a_593_);
v___x_596_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_snd_595_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = l_Lean_ConstantInfo_type(v_a_597_);
lean_dec(v_a_597_);
v___x_599_ = l_Lean_Expr_getForallBody(v___x_598_);
lean_dec_ref(v___x_598_);
if (lean_obj_tag(v___x_599_) == 4)
{
lean_object* v_declName_600_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___x_627_; lean_object* v_env_628_; uint8_t v___x_629_; 
v_declName_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc_n(v_declName_600_, 2);
lean_dec_ref_known(v___x_599_, 2);
v___x_627_ = lean_st_ref_get(v_a_584_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_628_);
lean_dec(v___x_627_);
v___x_629_ = l_Lean_isStructure(v_env_628_, v_declName_600_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_inc(v_fst_594_);
v___x_630_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_594_, v_structName_579_, lean_box(0), v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_dec_ref_known(v___x_630_, 1);
v___y_602_ = v_a_581_;
v___y_603_ = v_a_582_;
v___y_604_ = v_a_583_;
v___y_605_ = v_a_584_;
goto v___jp_601_;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_declName_600_);
lean_dec(v_fst_594_);
lean_dec_ref(v_str_591_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_dec(v_structName_579_);
v___y_602_ = v_a_581_;
v___y_603_ = v_a_582_;
v___y_604_ = v_a_583_;
v___y_605_ = v_a_584_;
goto v___jp_601_;
}
v___jp_601_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_box(0);
v___x_607_ = l_Lean_Name_str___override(v___x_606_, v_str_591_);
v___x_608_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_declName_600_, v___x_607_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_626_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_626_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_626_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_626_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
v_fst_613_ = lean_ctor_get(v_a_609_, 0);
v_snd_614_ = lean_ctor_get(v_a_609_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_609_);
if (v_isSharedCheck_625_ == 0)
{
v___x_616_ = v_a_609_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snd_614_);
lean_inc(v_fst_613_);
lean_dec(v_a_609_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_Name_append(v_fst_594_, v_fst_613_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_snd_614_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_620_);
v___x_622_ = v___x_611_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_dec(v_fst_594_);
return v___x_608_;
}
}
}
else
{
lean_object* v___x_639_; 
lean_dec_ref(v___x_599_);
lean_dec_ref(v_str_591_);
v___x_639_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_594_, v_structName_579_, lean_box(0), v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_639_;
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_fst_594_);
lean_dec_ref(v_str_591_);
lean_dec(v_structName_579_);
v_a_640_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_596_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_596_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_dec_ref(v_str_591_);
lean_dec(v_structName_579_);
return v___x_592_;
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_field_580_);
lean_dec(v_structName_579_);
v___x_648_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1);
v___x_649_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_648_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___boxed(lean_object* v_structName_650_, lean_object* v_field_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_650_, v_field_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(lean_object* v_00_u03b1_658_, lean_object* v_constName_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___boxed(lean_object* v_00_u03b1_666_, lean_object* v_constName_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(v_00_u03b1_666_, v_constName_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_674_, lean_object* v_ref_675_, lean_object* v_constName_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_675_, v_constName_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_683_, lean_object* v_ref_684_, lean_object* v_constName_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(v_00_u03b1_683_, v_ref_684_, v_constName_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v_ref_684_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_692_, lean_object* v_ref_693_, lean_object* v_msg_694_, lean_object* v_declHint_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_693_, v_msg_694_, v_declHint_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_702_, lean_object* v_ref_703_, lean_object* v_msg_704_, lean_object* v_declHint_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_702_, v_ref_703_, v_msg_704_, v_declHint_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v_ref_703_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_712_, lean_object* v_declHint_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_712_, v_declHint_713_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_720_, lean_object* v_declHint_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_720_, v_declHint_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_728_, lean_object* v_ref_729_, lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_729_, v_msg_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_737_, lean_object* v_ref_738_, lean_object* v_msg_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_737_, v_ref_738_, v_msg_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v_ref_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(lean_object* v_e_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = l_Lean_Expr_hasMVar(v_e_746_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_e_746_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; lean_object* v_mctx_752_; lean_object* v___x_753_; lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_756_; lean_object* v_cache_757_; lean_object* v_zetaDeltaFVarIds_758_; lean_object* v_postponed_759_; lean_object* v_diag_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_769_; 
v___x_751_ = lean_st_ref_get(v___y_747_);
v_mctx_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_ref(v_mctx_752_);
lean_dec(v___x_751_);
v___x_753_ = l_Lean_instantiateMVarsCore(v_mctx_752_, v_e_746_);
v_fst_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_fst_754_);
v_snd_755_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_snd_755_);
lean_dec_ref(v___x_753_);
v___x_756_ = lean_st_ref_take(v___y_747_);
v_cache_757_ = lean_ctor_get(v___x_756_, 1);
v_zetaDeltaFVarIds_758_ = lean_ctor_get(v___x_756_, 2);
v_postponed_759_ = lean_ctor_get(v___x_756_, 3);
v_diag_760_ = lean_ctor_get(v___x_756_, 4);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_756_, 0);
lean_dec(v_unused_770_);
v___x_762_ = v___x_756_;
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_diag_760_);
lean_inc(v_postponed_759_);
lean_inc(v_zetaDeltaFVarIds_758_);
lean_inc(v_cache_757_);
lean_dec(v___x_756_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_snd_755_);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_snd_755_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_cache_757_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_zetaDeltaFVarIds_758_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_postponed_759_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_diag_760_);
v___x_765_ = v_reuseFailAlloc_768_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_st_ref_put(v___y_747_, v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_fst_754_);
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg___boxed(lean_object* v_e_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_771_, v___y_772_);
lean_dec(v___y_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(lean_object* v_e_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_775_, v___y_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___boxed(lean_object* v_e_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(v_e_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
v___x_801_ = lean_apply_7(v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed(lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(v_x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(lean_object* v_lctx_811_, lean_object* v_localInsts_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; 
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_821_, 0, v_x_813_);
lean_closure_set(v___f_821_, 1, v___y_814_);
lean_closure_set(v___f_821_, 2, v___y_815_);
v___x_822_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_811_, v_localInsts_812_, v___f_821_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_822_) == 0)
{
return v___x_822_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___boxed(lean_object* v_lctx_831_, lean_object* v_localInsts_832_, lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_831_, v_localInsts_832_, v_x_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(lean_object* v_00_u03b1_842_, lean_object* v_lctx_843_, lean_object* v_localInsts_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_843_, v_localInsts_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed(lean_object* v_00_u03b1_854_, lean_object* v_lctx_855_, lean_object* v_localInsts_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(v_00_u03b1_854_, v_lctx_855_, v_localInsts_856_, v_x_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl(lean_box(0), v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_874_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_874_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg___boxed(lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(lean_object* v_00_u03b1_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___boxed(lean_object* v_00_u03b1_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(v_00_u03b1_910_, v_x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_919_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6(void){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Array_mkArray0(lean_box(0));
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(lean_object* v_structName_948_, lean_object* v_source_x3f_949_, lean_object* v_fields_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
if (lean_obj_tag(v_source_x3f_949_) == 0)
{
lean_object* v_ref_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_ref_958_ = lean_ctor_get(v___y_955_, 5);
v___x_959_ = 0;
v___x_960_ = l_Lean_SourceInfo_fromRef(v_ref_958_, v___x_959_);
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_960_, 8);
v___x_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_960_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_965_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_960_);
lean_ctor_set(v___x_966_, 1, v___x_964_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
v___x_967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_969_ = l_Lean_Syntax_SepArray_ofElems(v___x_968_, v_fields_950_);
v___x_970_ = l_Array_append___redArg(v___x_965_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_971_, 0, v___x_960_);
lean_ctor_set(v___x_971_, 1, v___x_964_);
lean_ctor_set(v___x_971_, 2, v___x_970_);
v___x_972_ = l_Lean_Syntax_node1(v___x_960_, v___x_967_, v___x_971_);
v___x_973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_966_);
v___x_974_ = l_Lean_Syntax_node1(v___x_960_, v___x_973_, v___x_966_);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_960_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_mkCIdent(v_structName_948_);
v___x_978_ = l_Lean_Syntax_node2(v___x_960_, v___x_964_, v___x_976_, v___x_977_);
v___x_979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_960_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Syntax_node6(v___x_960_, v___x_961_, v___x_963_, v___x_966_, v___x_972_, v___x_974_, v___x_978_, v___x_980_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1018_; 
v_val_983_ = lean_ctor_get(v_source_x3f_949_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_source_x3f_949_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_985_ = v_source_x3f_949_;
v_isShared_986_ = v_isSharedCheck_1018_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_val_983_);
lean_dec(v_source_x3f_949_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1018_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v_ref_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v_ref_987_ = lean_ctor_get(v___y_955_, 5);
v___x_988_ = 0;
v___x_989_ = l_Lean_SourceInfo_fromRef(v_ref_987_, v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_989_, 11);
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_989_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_994_ = l_Lean_Syntax_node1(v___x_989_, v___x_993_, v_val_983_);
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_989_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Lean_Syntax_node2(v___x_989_, v___x_993_, v___x_994_, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_999_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_1001_ = l_Lean_Syntax_SepArray_ofElems(v___x_1000_, v_fields_950_);
v___x_1002_ = l_Array_append___redArg(v___x_999_, v___x_1001_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___x_989_);
lean_ctor_set(v___x_1003_, 1, v___x_993_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node1(v___x_989_, v___x_998_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___x_989_);
lean_ctor_set(v___x_1006_, 1, v___x_993_);
lean_ctor_set(v___x_1006_, 2, v___x_999_);
v___x_1007_ = l_Lean_Syntax_node1(v___x_989_, v___x_1005_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_989_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_mkCIdent(v_structName_948_);
v___x_1011_ = l_Lean_Syntax_node2(v___x_989_, v___x_993_, v___x_1009_, v___x_1010_);
v___x_1012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_989_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node6(v___x_989_, v___x_990_, v___x_992_, v___x_997_, v___x_1004_, v___x_1007_, v___x_1011_, v___x_1013_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 0, v___x_1014_);
v___x_1016_ = v___x_985_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed(lean_object* v_structName_1019_, lean_object* v_source_x3f_1020_, lean_object* v_fields_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_1019_, v_source_x3f_1020_, v_fields_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_fields_1021_);
return v_res_1029_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_1047_ = l_String_toRawSubstring_x27(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(lean_object* v_a_1097_, lean_object* v_structName_1098_, lean_object* v_____r_1099_, lean_object* v_source_x3f_1100_, lean_object* v_seenFields_1101_, lean_object* v_fields_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_value_1110_; lean_object* v_ref_1111_; lean_object* v_quotContext_1112_; lean_object* v_currMacroScope_1113_; lean_object* v_ref_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_value_1110_ = lean_ctor_get(v_a_1097_, 2);
lean_inc(v_value_1110_);
lean_dec_ref(v_a_1097_);
v_ref_1111_ = lean_ctor_get(v___y_1107_, 5);
v_quotContext_1112_ = lean_ctor_get(v___y_1107_, 10);
v_currMacroScope_1113_ = lean_ctor_get(v___y_1107_, 11);
v_ref_1114_ = l_Lean_replaceRef(v_value_1110_, v_ref_1111_);
v___x_1115_ = 0;
v___x_1116_ = l_Lean_SourceInfo_fromRef(v_ref_1114_, v___x_1115_);
lean_dec(v_ref_1114_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1));
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_1116_, 8);
v___x_1120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1116_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_1122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_1123_ = lean_box(0);
lean_inc(v_currMacroScope_1113_);
lean_inc(v_quotContext_1112_);
v___x_1124_ = l_Lean_addMacroScope(v_quotContext_1112_, v___x_1123_, v_currMacroScope_1113_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_1126_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1116_);
lean_ctor_set(v___x_1126_, 1, v___x_1122_);
lean_ctor_set(v___x_1126_, 2, v___x_1124_);
lean_ctor_set(v___x_1126_, 3, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node1(v___x_1116_, v___x_1121_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node2(v___x_1116_, v___x_1118_, v___x_1120_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1116_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_1132_ = l_Lean_mkCIdent(v_structName_1098_);
lean_inc(v___x_1132_);
v___x_1133_ = l_Lean_Syntax_node1(v___x_1116_, v___x_1131_, v___x_1132_);
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_1135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1116_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
lean_inc_ref(v___x_1130_);
v___x_1136_ = l_Lean_Syntax_node5(v___x_1116_, v___x_1117_, v___x_1128_, v_value_1110_, v___x_1130_, v___x_1133_, v___x_1135_);
if (lean_obj_tag(v_source_x3f_1100_) == 1)
{
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1168_; 
v_val_1137_ = lean_ctor_get(v_source_x3f_1100_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_source_x3f_1100_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1139_ = v_source_x3f_1100_;
v_isShared_1140_ = v_isSharedCheck_1168_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v_source_x3f_1100_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1168_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_1116_, 10);
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1116_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27));
v___x_1145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1116_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node3(v___x_1116_, v___x_1131_, v___x_1136_, v___x_1145_, v_val_1137_);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_1148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1116_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_Syntax_node2(v___x_1116_, v___x_1131_, v___x_1146_, v___x_1148_);
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_1151_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_1152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1116_);
lean_ctor_set(v___x_1152_, 1, v___x_1131_);
lean_ctor_set(v___x_1152_, 2, v___x_1151_);
lean_inc_ref(v___x_1152_);
v___x_1153_ = l_Lean_Syntax_node1(v___x_1116_, v___x_1150_, v___x_1152_);
v___x_1154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1155_ = l_Lean_Syntax_node1(v___x_1116_, v___x_1154_, v___x_1152_);
v___x_1156_ = l_Lean_Syntax_node2(v___x_1116_, v___x_1131_, v___x_1130_, v___x_1132_);
v___x_1157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1116_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_Syntax_node6(v___x_1116_, v___x_1141_, v___x_1143_, v___x_1149_, v___x_1153_, v___x_1155_, v___x_1156_, v___x_1158_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1159_);
v___x_1161_ = v___x_1139_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_seenFields_1101_);
lean_ctor_set(v___x_1163_, 1, v_fields_1102_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1161_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1162_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v___x_1132_);
lean_dec_ref_known(v___x_1130_, 2);
lean_dec(v___x_1116_);
lean_dec(v_source_x3f_1100_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1136_);
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_seenFields_1101_);
lean_ctor_set(v___x_1171_, 1, v_fields_1102_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1170_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___boxed(lean_object* v_a_1175_, lean_object* v_structName_1176_, lean_object* v_____r_1177_, lean_object* v_source_x3f_1178_, lean_object* v_seenFields_1179_, lean_object* v_fields_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_1175_, v_structName_1176_, v_____r_1177_, v_source_x3f_1178_, v_seenFields_1179_, v_fields_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(lean_object* v_opts_1189_, lean_object* v_opt_1190_){
_start:
{
lean_object* v_name_1191_; lean_object* v_defValue_1192_; lean_object* v_map_1193_; lean_object* v___x_1194_; 
v_name_1191_ = lean_ctor_get(v_opt_1190_, 0);
v_defValue_1192_ = lean_ctor_get(v_opt_1190_, 1);
v_map_1193_ = lean_ctor_get(v_opts_1189_, 0);
v___x_1194_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1193_, v_name_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_unbox(v_defValue_1192_);
return v___x_1195_;
}
else
{
lean_object* v_val_1196_; 
v_val_1196_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v___x_1194_, 1);
if (lean_obj_tag(v_val_1196_) == 1)
{
uint8_t v_v_1197_; 
v_v_1197_ = lean_ctor_get_uint8(v_val_1196_, 0);
lean_dec_ref_known(v_val_1196_, 0);
return v_v_1197_;
}
else
{
uint8_t v___x_1198_; 
lean_dec(v_val_1196_);
v___x_1198_ = lean_unbox(v_defValue_1192_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_opts_1199_, lean_object* v_opt_1200_){
_start:
{
uint8_t v_res_1201_; lean_object* v_r_1202_; 
v_res_1201_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_opts_1199_, v_opt_1200_);
lean_dec_ref(v_opt_1200_);
lean_dec_ref(v_opts_1199_);
v_r_1202_ = lean_box(v_res_1201_);
return v_r_1202_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_box(1);
v___x_1204_ = l_Lean_MessageData_ofFormat(v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2));
v___x_1209_ = l_Lean_MessageData_ofFormat(v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
return v_x_1210_;
}
else
{
lean_object* v_head_1212_; lean_object* v_tail_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1235_; 
v_head_1212_ = lean_ctor_get(v_x_1211_, 0);
v_tail_1213_ = lean_ctor_get(v_x_1211_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1211_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1215_ = v_x_1211_;
v_isShared_1216_ = v_isSharedCheck_1235_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_tail_1213_);
lean_inc(v_head_1212_);
lean_dec(v_x_1211_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1235_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_before_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1233_; 
v_before_1217_ = lean_ctor_get(v_head_1212_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_head_1212_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_head_1212_, 1);
lean_dec(v_unused_1234_);
v___x_1219_ = v_head_1212_;
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_before_1217_);
lean_dec(v_head_1212_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 7);
lean_ctor_set(v___x_1219_, 1, v___x_1221_);
lean_ctor_set(v___x_1219_, 0, v_x_1210_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_x_1210_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3);
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 7);
lean_ctor_set(v___x_1215_, 1, v___x_1224_);
lean_ctor_set(v___x_1215_, 0, v___x_1223_);
v___x_1226_ = v___x_1215_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = l_Lean_MessageData_ofSyntax(v_before_1217_);
v___x_1228_ = l_Lean_indentD(v___x_1227_);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v_x_1210_ = v___x_1229_;
v_x_1211_ = v_tail_1213_;
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
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1));
v___x_1240_ = l_Lean_MessageData_ofFormat(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(lean_object* v_msgData_1241_, lean_object* v_macroStack_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_options_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_options_1245_ = lean_ctor_get(v___y_1243_, 2);
v___x_1246_ = l_Lean_Elab_pp_macroStack;
v___x_1247_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_options_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; 
lean_dec(v_macroStack_1242_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_msgData_1241_);
return v___x_1248_;
}
else
{
if (lean_obj_tag(v_macroStack_1242_) == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_msgData_1241_);
return v___x_1249_;
}
else
{
lean_object* v_head_1250_; lean_object* v_after_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1266_; 
v_head_1250_ = lean_ctor_get(v_macroStack_1242_, 0);
lean_inc(v_head_1250_);
v_after_1251_ = lean_ctor_get(v_head_1250_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_head_1250_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_head_1250_, 0);
lean_dec(v_unused_1267_);
v___x_1253_ = v_head_1250_;
v_isShared_1254_ = v_isSharedCheck_1266_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_after_1251_);
lean_dec(v_head_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1266_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 7);
lean_ctor_set(v___x_1253_, 1, v___x_1255_);
lean_ctor_set(v___x_1253_, 0, v_msgData_1241_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_msgData_1241_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_msgData_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1258_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_MessageData_ofSyntax(v_after_1251_);
v___x_1261_ = l_Lean_indentD(v___x_1260_);
v_msgData_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1262_, 0, v___x_1259_);
lean_ctor_set(v_msgData_1262_, 1, v___x_1261_);
v___x_1263_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(v_msgData_1262_, v_macroStack_1242_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___boxed(lean_object* v_msgData_1268_, lean_object* v_macroStack_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_1268_, v_macroStack_1269_, v___y_1270_);
lean_dec_ref(v___y_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(lean_object* v_msg_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_ref_1281_; lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v_macroStack_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_ref_1281_ = lean_ctor_get(v___y_1278_, 5);
v___x_1282_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_1273_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v_macroStack_1284_ = lean_ctor_get(v___y_1274_, 1);
v___x_1285_ = l_Lean_Elab_getBetterRef(v_ref_1281_, v_macroStack_1284_);
lean_inc(v_macroStack_1284_);
v___x_1286_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_a_1283_, v_macroStack_1284_, v___y_1278_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1285_);
lean_ctor_set(v___x_1291_, 1, v_a_1287_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 1);
lean_ctor_set(v___x_1289_, 0, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg___boxed(lean_object* v_msg_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(lean_object* v_ref_1305_, lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_fileName_1314_; lean_object* v_fileMap_1315_; lean_object* v_options_1316_; lean_object* v_currRecDepth_1317_; lean_object* v_maxRecDepth_1318_; lean_object* v_ref_1319_; lean_object* v_currNamespace_1320_; lean_object* v_openDecls_1321_; lean_object* v_initHeartbeats_1322_; lean_object* v_maxHeartbeats_1323_; lean_object* v_quotContext_1324_; lean_object* v_currMacroScope_1325_; uint8_t v_diag_1326_; lean_object* v_cancelTk_x3f_1327_; uint8_t v_suppressElabErrors_1328_; lean_object* v_inheritedTraceOptions_1329_; lean_object* v_ref_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_fileName_1314_ = lean_ctor_get(v___y_1311_, 0);
v_fileMap_1315_ = lean_ctor_get(v___y_1311_, 1);
v_options_1316_ = lean_ctor_get(v___y_1311_, 2);
v_currRecDepth_1317_ = lean_ctor_get(v___y_1311_, 3);
v_maxRecDepth_1318_ = lean_ctor_get(v___y_1311_, 4);
v_ref_1319_ = lean_ctor_get(v___y_1311_, 5);
v_currNamespace_1320_ = lean_ctor_get(v___y_1311_, 6);
v_openDecls_1321_ = lean_ctor_get(v___y_1311_, 7);
v_initHeartbeats_1322_ = lean_ctor_get(v___y_1311_, 8);
v_maxHeartbeats_1323_ = lean_ctor_get(v___y_1311_, 9);
v_quotContext_1324_ = lean_ctor_get(v___y_1311_, 10);
v_currMacroScope_1325_ = lean_ctor_get(v___y_1311_, 11);
v_diag_1326_ = lean_ctor_get_uint8(v___y_1311_, sizeof(void*)*14);
v_cancelTk_x3f_1327_ = lean_ctor_get(v___y_1311_, 12);
v_suppressElabErrors_1328_ = lean_ctor_get_uint8(v___y_1311_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1329_ = lean_ctor_get(v___y_1311_, 13);
v_ref_1330_ = l_Lean_replaceRef(v_ref_1305_, v_ref_1319_);
lean_inc_ref(v_inheritedTraceOptions_1329_);
lean_inc(v_cancelTk_x3f_1327_);
lean_inc(v_currMacroScope_1325_);
lean_inc(v_quotContext_1324_);
lean_inc(v_maxHeartbeats_1323_);
lean_inc(v_initHeartbeats_1322_);
lean_inc(v_openDecls_1321_);
lean_inc(v_currNamespace_1320_);
lean_inc(v_maxRecDepth_1318_);
lean_inc(v_currRecDepth_1317_);
lean_inc_ref(v_options_1316_);
lean_inc_ref(v_fileMap_1315_);
lean_inc_ref(v_fileName_1314_);
v___x_1331_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1331_, 0, v_fileName_1314_);
lean_ctor_set(v___x_1331_, 1, v_fileMap_1315_);
lean_ctor_set(v___x_1331_, 2, v_options_1316_);
lean_ctor_set(v___x_1331_, 3, v_currRecDepth_1317_);
lean_ctor_set(v___x_1331_, 4, v_maxRecDepth_1318_);
lean_ctor_set(v___x_1331_, 5, v_ref_1330_);
lean_ctor_set(v___x_1331_, 6, v_currNamespace_1320_);
lean_ctor_set(v___x_1331_, 7, v_openDecls_1321_);
lean_ctor_set(v___x_1331_, 8, v_initHeartbeats_1322_);
lean_ctor_set(v___x_1331_, 9, v_maxHeartbeats_1323_);
lean_ctor_set(v___x_1331_, 10, v_quotContext_1324_);
lean_ctor_set(v___x_1331_, 11, v_currMacroScope_1325_);
lean_ctor_set(v___x_1331_, 12, v_cancelTk_x3f_1327_);
lean_ctor_set(v___x_1331_, 13, v_inheritedTraceOptions_1329_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*14, v_diag_1326_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*14 + 1, v_suppressElabErrors_1328_);
v___x_1332_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___x_1331_, v___y_1312_);
lean_dec_ref_known(v___x_1331_, 14);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg___boxed(lean_object* v_ref_1333_, lean_object* v_msg_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1333_, v_msg_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v_ref_1333_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(lean_object* v_msg_1343_, lean_object* v_declHint_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_env_1348_; uint8_t v___x_1349_; 
v___x_1347_ = lean_st_ref_get(v___y_1345_);
v_env_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_env_1348_);
lean_dec(v___x_1347_);
v___x_1349_ = l_Lean_Name_isAnonymous(v_declHint_1344_);
if (v___x_1349_ == 0)
{
uint8_t v_isExporting_1350_; 
v_isExporting_1350_ = lean_ctor_get_uint8(v_env_1348_, sizeof(void*)*8);
if (v_isExporting_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref(v_env_1348_);
lean_dec(v_declHint_1344_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_msg_1343_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
lean_inc_ref(v_env_1348_);
v___x_1352_ = l_Lean_Environment_setExporting(v_env_1348_, v___x_1349_);
lean_inc(v_declHint_1344_);
lean_inc_ref(v___x_1352_);
v___x_1353_ = l_Lean_Environment_contains(v___x_1352_, v_declHint_1344_, v_isExporting_1350_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref(v___x_1352_);
lean_dec_ref(v_env_1348_);
lean_dec(v_declHint_1344_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_msg_1343_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_c_1362_; lean_object* v___x_1363_; 
v___x_1355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1356_ = lean_unsigned_to_nat(32u);
v___x_1357_ = lean_mk_empty_array_with_capacity(v___x_1356_);
lean_dec_ref(v___x_1357_);
v___x_1358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1359_ = l_Lean_Options_empty;
v___x_1360_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1352_);
lean_ctor_set(v___x_1360_, 1, v___x_1355_);
lean_ctor_set(v___x_1360_, 2, v___x_1358_);
lean_ctor_set(v___x_1360_, 3, v___x_1359_);
lean_inc(v_declHint_1344_);
v___x_1361_ = l_Lean_MessageData_ofConstName(v_declHint_1344_, v___x_1349_);
v_c_1362_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1362_, 0, v___x_1360_);
lean_ctor_set(v_c_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1348_, v_declHint_1344_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v_env_1348_);
lean_dec(v_declHint_1344_);
v___x_1364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v_c_1362_);
v___x_1366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_MessageData_note(v___x_1367_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_msg_1343_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
else
{
lean_object* v_val_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1406_; 
v_val_1371_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1373_ = v___x_1363_;
v_isShared_1374_ = v_isSharedCheck_1406_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_val_1371_);
lean_dec(v___x_1363_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1406_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_mod_1378_; uint8_t v___x_1379_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lean_Environment_header(v_env_1348_);
lean_dec_ref(v_env_1348_);
v___x_1377_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1376_);
v_mod_1378_ = lean_array_get(v___x_1375_, v___x_1377_, v_val_1371_);
lean_dec(v_val_1371_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = l_Lean_isPrivateName(v_declHint_1344_);
lean_dec(v_declHint_1344_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v_c_1362_);
v___x_1382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_MessageData_ofName(v_mod_1378_);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_MessageData_note(v___x_1387_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_msg_1343_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1389_);
v___x_1391_ = v___x_1373_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
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
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1393_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v_c_1362_);
v___x_1395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_MessageData_ofName(v_mod_1378_);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = l_Lean_MessageData_note(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_msg_1343_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1402_);
v___x_1404_ = v___x_1373_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1407_; 
lean_dec_ref(v_env_1348_);
lean_dec(v_declHint_1344_);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_msg_1343_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg___boxed(lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1408_, v_declHint_1409_, v___y_1410_);
lean_dec(v___y_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(lean_object* v_msg_1413_, lean_object* v_declHint_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1432_; 
v___x_1422_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1413_, v_declHint_1414_, v___y_1420_);
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = l_Lean_unknownIdentifierMessageTag;
v___x_1428_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v_a_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1428_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23___boxed(lean_object* v_msg_1433_, lean_object* v_declHint_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1433_, v_declHint_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(lean_object* v_ref_1443_, lean_object* v_msg_1444_, lean_object* v_declHint_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1444_, v_declHint_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1443_, v_a_1454_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg___boxed(lean_object* v_ref_1456_, lean_object* v_msg_1457_, lean_object* v_declHint_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1456_, v_msg_1457_, v_declHint_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v_ref_1456_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(lean_object* v_ref_1467_, lean_object* v_constName_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1476_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1477_ = 0;
lean_inc(v_constName_1468_);
v___x_1478_ = l_Lean_MessageData_ofConstName(v_constName_1468_, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1476_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1467_, v___x_1481_, v_constName_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_ref_1483_, lean_object* v_constName_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1483_, v_constName_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_ref_1483_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(lean_object* v_constName_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_ref_1501_; lean_object* v___x_1502_; 
v_ref_1501_ = lean_ctor_get(v___y_1498_, 5);
v___x_1502_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1501_, v_constName_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg___boxed(lean_object* v_constName_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(lean_object* v_constName_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v_env_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1520_ = lean_st_ref_get(v___y_1518_);
v_env_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc_ref(v_env_1521_);
lean_dec(v___x_1520_);
v___x_1522_ = 0;
lean_inc(v_constName_1512_);
v___x_1523_ = l_Lean_Environment_find_x3f(v_env_1521_, v_constName_1512_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_constName_1512_);
v_val_1525_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1523_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v___x_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 0);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_val_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2___boxed(lean_object* v_constName_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_constName_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1541_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(uint8_t v_suppressElabErrors_1548_, uint8_t v___y_1549_, lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 1)
{
lean_object* v_pre_1551_; 
v_pre_1551_ = lean_ctor_get(v_x_1550_, 0);
switch(lean_obj_tag(v_pre_1551_))
{
case 1:
{
lean_object* v_pre_1552_; 
v_pre_1552_ = lean_ctor_get(v_pre_1551_, 0);
switch(lean_obj_tag(v_pre_1552_))
{
case 0:
{
lean_object* v_str_1553_; lean_object* v_str_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_str_1553_ = lean_ctor_get(v_x_1550_, 1);
v_str_1554_ = lean_ctor_get(v_pre_1551_, 1);
v___x_1555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8));
v___x_1556_ = lean_string_dec_eq(v_str_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2));
v___x_1558_ = lean_string_dec_eq(v_str_1554_, v___x_1557_);
if (v___x_1558_ == 0)
{
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___x_1560_ = lean_string_dec_eq(v_str_1553_, v___x_1559_);
if (v___x_1560_ == 0)
{
return v___x_1560_;
}
else
{
return v_suppressElabErrors_1548_;
}
}
}
else
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1));
v___x_1562_ = lean_string_dec_eq(v_str_1553_, v___x_1561_);
if (v___x_1562_ == 0)
{
return v___x_1562_;
}
else
{
return v_suppressElabErrors_1548_;
}
}
}
case 1:
{
lean_object* v_pre_1563_; 
v_pre_1563_ = lean_ctor_get(v_pre_1552_, 0);
if (lean_obj_tag(v_pre_1563_) == 0)
{
lean_object* v_str_1564_; lean_object* v_str_1565_; lean_object* v_str_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_str_1564_ = lean_ctor_get(v_x_1550_, 1);
v_str_1565_ = lean_ctor_get(v_pre_1551_, 1);
v_str_1566_ = lean_ctor_get(v_pre_1552_, 1);
v___x_1567_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2));
v___x_1568_ = lean_string_dec_eq(v_str_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3));
v___x_1570_ = lean_string_dec_eq(v_str_1565_, v___x_1569_);
if (v___x_1570_ == 0)
{
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4));
v___x_1572_ = lean_string_dec_eq(v_str_1564_, v___x_1571_);
if (v___x_1572_ == 0)
{
return v___x_1572_;
}
else
{
return v_suppressElabErrors_1548_;
}
}
}
}
else
{
return v___y_1549_;
}
}
default: 
{
return v___y_1549_;
}
}
}
case 0:
{
lean_object* v_str_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_str_1573_ = lean_ctor_get(v_x_1550_, 1);
v___x_1574_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5));
v___x_1575_ = lean_string_dec_eq(v_str_1573_, v___x_1574_);
if (v___x_1575_ == 0)
{
return v___x_1575_;
}
else
{
return v_suppressElabErrors_1548_;
}
}
default: 
{
return v___y_1549_;
}
}
}
else
{
return v___y_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1576_, lean_object* v___y_1577_, lean_object* v_x_1578_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1579_; uint8_t v___y_50669__boxed_1580_; uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_suppressElabErrors_boxed_1579_ = lean_unbox(v_suppressElabErrors_1576_);
v___y_50669__boxed_1580_ = lean_unbox(v___y_1577_);
v_res_1581_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(v_suppressElabErrors_boxed_1579_, v___y_50669__boxed_1580_, v_x_1578_);
lean_dec(v_x_1578_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1583_, lean_object* v_msgData_1584_, uint8_t v_severity_1585_, uint8_t v_isSilent_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; uint8_t v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1654_; uint8_t v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1665_; uint8_t v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; uint8_t v___y_1670_; uint8_t v___y_1671_; uint8_t v___x_1676_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v___y_1682_; uint8_t v___y_1683_; uint8_t v___y_1684_; uint8_t v___y_1686_; uint8_t v___x_1701_; 
v___x_1676_ = 2;
v___x_1701_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1585_, v___x_1676_);
if (v___x_1701_ == 0)
{
v___y_1686_ = v___x_1701_;
goto v___jp_1685_;
}
else
{
uint8_t v___x_1702_; 
lean_inc_ref(v_msgData_1584_);
v___x_1702_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1584_);
v___y_1686_ = v___x_1702_;
goto v___jp_1685_;
}
v___jp_1592_:
{
lean_object* v___x_1602_; lean_object* v_currNamespace_1603_; lean_object* v_openDecls_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_traceState_1609_; lean_object* v_cache_1610_; lean_object* v_messages_1611_; lean_object* v_infoState_1612_; lean_object* v_snapshotTasks_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1627_; 
v___x_1602_ = lean_st_ref_take(v___y_1601_);
v_currNamespace_1603_ = lean_ctor_get(v___y_1600_, 6);
v_openDecls_1604_ = lean_ctor_get(v___y_1600_, 7);
v_env_1605_ = lean_ctor_get(v___x_1602_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1602_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1602_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1602_, 3);
v_traceState_1609_ = lean_ctor_get(v___x_1602_, 4);
v_cache_1610_ = lean_ctor_get(v___x_1602_, 5);
v_messages_1611_ = lean_ctor_get(v___x_1602_, 6);
v_infoState_1612_ = lean_ctor_get(v___x_1602_, 7);
v_snapshotTasks_1613_ = lean_ctor_get(v___x_1602_, 8);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1615_ = v___x_1602_;
v_isShared_1616_ = v_isSharedCheck_1627_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_snapshotTasks_1613_);
lean_inc(v_infoState_1612_);
lean_inc(v_messages_1611_);
lean_inc(v_cache_1610_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1627_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_inc(v_openDecls_1604_);
lean_inc(v_currNamespace_1603_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_currNamespace_1603_);
lean_ctor_set(v___x_1617_, 1, v_openDecls_1604_);
v___x_1618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___y_1599_);
lean_inc_ref(v___y_1594_);
lean_inc_ref(v___y_1597_);
v___x_1619_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1619_, 0, v___y_1597_);
lean_ctor_set(v___x_1619_, 1, v___y_1595_);
lean_ctor_set(v___x_1619_, 2, v___y_1598_);
lean_ctor_set(v___x_1619_, 3, v___y_1594_);
lean_ctor_set(v___x_1619_, 4, v___x_1618_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*5, v___y_1593_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*5 + 1, v___y_1596_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*5 + 2, v_isSilent_1586_);
v___x_1620_ = l_Lean_MessageLog_add(v___x_1619_, v_messages_1611_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 6, v___x_1620_);
v___x_1622_ = v___x_1615_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_env_1605_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_traceState_1609_);
lean_ctor_set(v_reuseFailAlloc_1626_, 5, v_cache_1610_);
lean_ctor_set(v_reuseFailAlloc_1626_, 6, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1626_, 7, v_infoState_1612_);
lean_ctor_set(v_reuseFailAlloc_1626_, 8, v_snapshotTasks_1613_);
v___x_1622_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_st_ref_put(v___y_1601_, v___x_1622_);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
v___jp_1628_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1652_; 
v___x_1637_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1584_);
v___x_1638_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v___x_1637_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1652_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1652_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_inc_ref_n(v___y_1634_, 2);
v___x_1643_ = l_Lean_FileMap_toPosition(v___y_1634_, v___y_1631_);
lean_dec(v___y_1631_);
v___x_1644_ = l_Lean_FileMap_toPosition(v___y_1634_, v___y_1636_);
lean_dec(v___y_1636_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
v___x_1646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
if (v___y_1635_ == 0)
{
lean_del_object(v___x_1641_);
lean_dec_ref(v___y_1629_);
v___y_1593_ = v___y_1630_;
v___y_1594_ = v___x_1646_;
v___y_1595_ = v___x_1643_;
v___y_1596_ = v___y_1633_;
v___y_1597_ = v___y_1632_;
v___y_1598_ = v___x_1645_;
v___y_1599_ = v_a_1639_;
v___y_1600_ = v___y_1589_;
v___y_1601_ = v___y_1590_;
goto v___jp_1592_;
}
else
{
uint8_t v___x_1647_; 
lean_inc(v_a_1639_);
v___x_1647_ = l_Lean_MessageData_hasTag(v___y_1629_, v_a_1639_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec_ref_known(v___x_1645_, 1);
lean_dec_ref(v___x_1643_);
lean_dec(v_a_1639_);
v___x_1648_ = lean_box(0);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1648_);
v___x_1650_ = v___x_1641_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
else
{
lean_del_object(v___x_1641_);
v___y_1593_ = v___y_1630_;
v___y_1594_ = v___x_1646_;
v___y_1595_ = v___x_1643_;
v___y_1596_ = v___y_1633_;
v___y_1597_ = v___y_1632_;
v___y_1598_ = v___x_1645_;
v___y_1599_ = v_a_1639_;
v___y_1600_ = v___y_1589_;
v___y_1601_ = v___y_1590_;
goto v___jp_1592_;
}
}
}
}
v___jp_1653_:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Syntax_getTailPos_x3f(v___y_1656_, v___y_1655_);
lean_dec(v___y_1656_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_inc(v___y_1661_);
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1661_;
v___y_1632_ = v___y_1658_;
v___y_1633_ = v___y_1657_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v___y_1661_;
goto v___jp_1628_;
}
else
{
lean_object* v_val_1663_; 
v_val_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1661_;
v___y_1632_ = v___y_1658_;
v___y_1633_ = v___y_1657_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v_val_1663_;
goto v___jp_1628_;
}
}
v___jp_1664_:
{
lean_object* v_ref_1672_; lean_object* v___x_1673_; 
v_ref_1672_ = l_Lean_replaceRef(v_ref_1583_, v___y_1667_);
v___x_1673_ = l_Lean_Syntax_getPos_x3f(v_ref_1672_, v___y_1666_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___y_1654_ = v___y_1665_;
v___y_1655_ = v___y_1666_;
v___y_1656_ = v_ref_1672_;
v___y_1657_ = v___y_1671_;
v___y_1658_ = v___y_1668_;
v___y_1659_ = v___y_1669_;
v___y_1660_ = v___y_1670_;
v___y_1661_ = v___x_1674_;
goto v___jp_1653_;
}
else
{
lean_object* v_val_1675_; 
v_val_1675_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v___x_1673_, 1);
v___y_1654_ = v___y_1665_;
v___y_1655_ = v___y_1666_;
v___y_1656_ = v_ref_1672_;
v___y_1657_ = v___y_1671_;
v___y_1658_ = v___y_1668_;
v___y_1659_ = v___y_1669_;
v___y_1660_ = v___y_1670_;
v___y_1661_ = v_val_1675_;
goto v___jp_1653_;
}
}
v___jp_1677_:
{
if (v___y_1684_ == 0)
{
v___y_1665_ = v___y_1681_;
v___y_1666_ = v___y_1683_;
v___y_1667_ = v___y_1678_;
v___y_1668_ = v___y_1679_;
v___y_1669_ = v___y_1680_;
v___y_1670_ = v___y_1682_;
v___y_1671_ = v_severity_1585_;
goto v___jp_1664_;
}
else
{
v___y_1665_ = v___y_1681_;
v___y_1666_ = v___y_1683_;
v___y_1667_ = v___y_1678_;
v___y_1668_ = v___y_1679_;
v___y_1669_ = v___y_1680_;
v___y_1670_ = v___y_1682_;
v___y_1671_ = v___x_1676_;
goto v___jp_1664_;
}
}
v___jp_1685_:
{
if (v___y_1686_ == 0)
{
lean_object* v_fileName_1687_; lean_object* v_fileMap_1688_; lean_object* v_options_1689_; lean_object* v_ref_1690_; uint8_t v_suppressElabErrors_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___f_1694_; uint8_t v___x_1695_; uint8_t v___x_1696_; 
v_fileName_1687_ = lean_ctor_get(v___y_1589_, 0);
v_fileMap_1688_ = lean_ctor_get(v___y_1589_, 1);
v_options_1689_ = lean_ctor_get(v___y_1589_, 2);
v_ref_1690_ = lean_ctor_get(v___y_1589_, 5);
v_suppressElabErrors_1691_ = lean_ctor_get_uint8(v___y_1589_, sizeof(void*)*14 + 1);
v___x_1692_ = lean_box(v_suppressElabErrors_1691_);
v___x_1693_ = lean_box(v___y_1686_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1694_, 0, v___x_1692_);
lean_closure_set(v___f_1694_, 1, v___x_1693_);
v___x_1695_ = 1;
v___x_1696_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1585_, v___x_1695_);
if (v___x_1696_ == 0)
{
v___y_1678_ = v_ref_1690_;
v___y_1679_ = v_fileName_1687_;
v___y_1680_ = v_fileMap_1688_;
v___y_1681_ = v___f_1694_;
v___y_1682_ = v_suppressElabErrors_1691_;
v___y_1683_ = v___y_1686_;
v___y_1684_ = v___x_1696_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = l_Lean_warningAsError;
v___x_1698_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_options_1689_, v___x_1697_);
v___y_1678_ = v_ref_1690_;
v___y_1679_ = v_fileName_1687_;
v___y_1680_ = v_fileMap_1688_;
v___y_1681_ = v___f_1694_;
v___y_1682_ = v_suppressElabErrors_1691_;
v___y_1683_ = v___y_1686_;
v___y_1684_ = v___x_1698_;
goto v___jp_1677_;
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec_ref(v_msgData_1584_);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1703_, lean_object* v_msgData_1704_, lean_object* v_severity_1705_, lean_object* v_isSilent_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v_severity_boxed_1712_; uint8_t v_isSilent_boxed_1713_; lean_object* v_res_1714_; 
v_severity_boxed_1712_ = lean_unbox(v_severity_1705_);
v_isSilent_boxed_1713_ = lean_unbox(v_isSilent_1706_);
v_res_1714_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1703_, v_msgData_1704_, v_severity_boxed_1712_, v_isSilent_boxed_1713_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v_ref_1703_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(lean_object* v_msgData_1715_, uint8_t v_severity_1716_, uint8_t v_isSilent_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_ref_1725_; lean_object* v___x_1726_; 
v_ref_1725_ = lean_ctor_get(v___y_1722_, 5);
v___x_1726_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1725_, v_msgData_1715_, v_severity_1716_, v_isSilent_1717_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1727_, lean_object* v_severity_1728_, lean_object* v_isSilent_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v_severity_boxed_1737_; uint8_t v_isSilent_boxed_1738_; lean_object* v_res_1739_; 
v_severity_boxed_1737_ = lean_unbox(v_severity_1728_);
v_isSilent_boxed_1738_ = lean_unbox(v_isSilent_1729_);
v_res_1739_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1727_, v_severity_boxed_1737_, v_isSilent_boxed_1738_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(lean_object* v_msgData_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = 2;
v___x_1749_ = 0;
v___x_1750_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1740_, v___x_1748_, v___x_1749_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1___boxed(lean_object* v_msgData_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v_msgData_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(lean_object* v_ref_1760_, lean_object* v_msgData_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = 2;
v___x_1770_ = 0;
v___x_1771_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1760_, v_msgData_1761_, v___x_1769_, v___x_1770_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0___boxed(lean_object* v_ref_1772_, lean_object* v_msgData_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1772_, v_msgData_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v_ref_1772_);
return v_res_1781_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(lean_object* v_ex_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
if (lean_obj_tag(v_ex_1785_) == 0)
{
lean_object* v_ref_1793_; lean_object* v_msg_1794_; lean_object* v___x_1795_; 
v_ref_1793_ = lean_ctor_get(v_ex_1785_, 0);
lean_inc(v_ref_1793_);
v_msg_1794_ = lean_ctor_get(v_ex_1785_, 1);
lean_inc_ref(v_msg_1794_);
lean_dec_ref_known(v_ex_1785_, 2);
v___x_1795_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1793_, v_msg_1794_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v_ref_1793_);
return v___x_1795_;
}
else
{
lean_object* v_id_1796_; uint8_t v___y_1798_; uint8_t v___x_1820_; 
v_id_1796_ = lean_ctor_get(v_ex_1785_, 0);
lean_inc(v_id_1796_);
v___x_1820_ = l_Lean_Elab_isAbortExceptionId(v_id_1796_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Lean_Exception_isInterrupt(v_ex_1785_);
lean_dec_ref_known(v_ex_1785_, 2);
v___y_1798_ = v___x_1821_;
goto v___jp_1797_;
}
else
{
lean_dec_ref_known(v_ex_1785_, 2);
v___y_1798_ = v___x_1820_;
goto v___jp_1797_;
}
v___jp_1797_:
{
if (v___y_1798_ == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_InternalExceptionId_getName(v_id_1796_);
lean_dec(v_id_1796_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1);
v___x_1802_ = l_Lean_MessageData_ofName(v_a_1800_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v___x_1803_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1804_;
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1817_; 
v_a_1805_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1807_ = v___x_1799_;
v_isShared_1808_ = v_isSharedCheck_1817_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1799_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1817_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_ref_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v_ref_1809_ = lean_ctor_get(v___y_1790_, 5);
v___x_1810_ = lean_io_error_to_string(v_a_1805_);
v___x_1811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
v___x_1812_ = l_Lean_MessageData_ofFormat(v___x_1811_);
lean_inc(v_ref_1809_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_ref_1809_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1813_);
v___x_1815_ = v___x_1807_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v_id_1796_);
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___boxed(lean_object* v_ex_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v_ex_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(lean_object* v_t_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; lean_object* v_infoState_1835_; uint8_t v_enabled_1836_; 
v___x_1834_ = lean_st_ref_get(v___y_1832_);
v_infoState_1835_ = lean_ctor_get(v___x_1834_, 7);
lean_inc_ref(v_infoState_1835_);
lean_dec(v___x_1834_);
v_enabled_1836_ = lean_ctor_get_uint8(v_infoState_1835_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1835_);
if (v_enabled_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec_ref(v_t_1831_);
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v_infoState_1840_; lean_object* v_env_1841_; lean_object* v_nextMacroScope_1842_; lean_object* v_ngen_1843_; lean_object* v_auxDeclNGen_1844_; lean_object* v_traceState_1845_; lean_object* v_cache_1846_; lean_object* v_messages_1847_; lean_object* v_snapshotTasks_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1870_; 
v___x_1839_ = lean_st_ref_take(v___y_1832_);
v_infoState_1840_ = lean_ctor_get(v___x_1839_, 7);
v_env_1841_ = lean_ctor_get(v___x_1839_, 0);
v_nextMacroScope_1842_ = lean_ctor_get(v___x_1839_, 1);
v_ngen_1843_ = lean_ctor_get(v___x_1839_, 2);
v_auxDeclNGen_1844_ = lean_ctor_get(v___x_1839_, 3);
v_traceState_1845_ = lean_ctor_get(v___x_1839_, 4);
v_cache_1846_ = lean_ctor_get(v___x_1839_, 5);
v_messages_1847_ = lean_ctor_get(v___x_1839_, 6);
v_snapshotTasks_1848_ = lean_ctor_get(v___x_1839_, 8);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1850_ = v___x_1839_;
v_isShared_1851_ = v_isSharedCheck_1870_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snapshotTasks_1848_);
lean_inc(v_infoState_1840_);
lean_inc(v_messages_1847_);
lean_inc(v_cache_1846_);
lean_inc(v_traceState_1845_);
lean_inc(v_auxDeclNGen_1844_);
lean_inc(v_ngen_1843_);
lean_inc(v_nextMacroScope_1842_);
lean_inc(v_env_1841_);
lean_dec(v___x_1839_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1870_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
uint8_t v_enabled_1852_; lean_object* v_assignment_1853_; lean_object* v_lazyAssignment_1854_; lean_object* v_trees_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1869_; 
v_enabled_1852_ = lean_ctor_get_uint8(v_infoState_1840_, sizeof(void*)*3);
v_assignment_1853_ = lean_ctor_get(v_infoState_1840_, 0);
v_lazyAssignment_1854_ = lean_ctor_get(v_infoState_1840_, 1);
v_trees_1855_ = lean_ctor_get(v_infoState_1840_, 2);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_infoState_1840_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1857_ = v_infoState_1840_;
v_isShared_1858_ = v_isSharedCheck_1869_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_trees_1855_);
lean_inc(v_lazyAssignment_1854_);
lean_inc(v_assignment_1853_);
lean_dec(v_infoState_1840_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1869_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = l_Lean_PersistentArray_push___redArg(v_trees_1855_, v_t_1831_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 2, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_assignment_1853_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_lazyAssignment_1854_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v___x_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, sizeof(void*)*3, v_enabled_1852_);
v___x_1861_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 7, v___x_1861_);
v___x_1863_ = v___x_1850_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_env_1841_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1842_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1843_);
lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1844_);
lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_traceState_1845_);
lean_ctor_set(v_reuseFailAlloc_1867_, 5, v_cache_1846_);
lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_messages_1847_);
lean_ctor_set(v_reuseFailAlloc_1867_, 7, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_snapshotTasks_1848_);
v___x_1863_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_st_ref_put(v___y_1832_, v___x_1863_);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_t_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_1871_, v___y_1872_);
lean_dec(v___y_1872_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_unsigned_to_nat(32u);
v___x_1876_ = lean_mk_empty_array_with_capacity(v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1878_ = ((size_t)5ULL);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_unsigned_to_nat(32u);
v___x_1881_ = lean_mk_empty_array_with_capacity(v___x_1880_);
v___x_1882_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0);
v___x_1883_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1881_);
lean_ctor_set(v___x_1883_, 2, v___x_1879_);
lean_ctor_set(v___x_1883_, 3, v___x_1879_);
lean_ctor_set_usize(v___x_1883_, 4, v___x_1878_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(lean_object* v_t_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_infoState_1893_; uint8_t v_enabled_1894_; 
v___x_1892_ = lean_st_ref_get(v___y_1890_);
v_infoState_1893_ = lean_ctor_get(v___x_1892_, 7);
lean_inc_ref(v_infoState_1893_);
lean_dec(v___x_1892_);
v_enabled_1894_ = lean_ctor_get_uint8(v_infoState_1893_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1893_);
if (v_enabled_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec_ref(v_t_1884_);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
v___x_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_t_1884_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v___x_1898_, v___y_1890_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___boxed(lean_object* v_t_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v_t_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(lean_object* v_info_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_info_1909_);
v___x_1918_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v___x_1917_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1___boxed(lean_object* v_info_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v_info_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13));
v___x_1967_ = l_String_toRawSubstring_x27(v___x_1966_);
return v___x_1967_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9));
v___x_1991_ = l_String_toRawSubstring_x27(v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(uint8_t v___x_2006_, lean_object* v_option_2007_, lean_object* v_fst_2008_, uint8_t v___x_2009_, lean_object* v_fst_2010_, lean_object* v_fst_2011_, lean_object* v_snd_2012_, lean_object* v_mkStructInst_2013_, lean_object* v_seenFields_2014_, lean_object* v_fields_2015_, lean_object* v_value_2016_, lean_object* v_____r_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___y_2026_; lean_object* v_source_x3f_2027_; lean_object* v_seenFields_2028_; lean_object* v_fields_2029_; lean_object* v___y_2030_; lean_object* v_value_2054_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8));
lean_inc(v_value_2016_);
v___x_2068_ = l_Lean_Syntax_isOfKind(v_value_2016_, v___x_2067_);
if (v___x_2068_ == 0)
{
v_value_2054_ = v_value_2016_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = l_Lean_Syntax_getArg(v_value_2016_, v___x_2069_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10));
lean_inc(v___x_2070_);
v___x_2100_ = l_Lean_Syntax_isOfKind(v___x_2070_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec(v___x_2070_);
v_value_2054_ = v_value_2016_;
goto v___jp_2053_;
}
else
{
goto v___jp_2071_;
}
}
else
{
goto v___jp_2071_;
}
v___jp_2071_:
{
lean_object* v_ref_2072_; lean_object* v_quotContext_2073_; lean_object* v_currMacroScope_2074_; lean_object* v_ref_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_ref_2072_ = lean_ctor_get(v___y_2022_, 5);
v_quotContext_2073_ = lean_ctor_get(v___y_2022_, 10);
v_currMacroScope_2074_ = lean_ctor_get(v___y_2022_, 11);
v_ref_2075_ = l_Lean_replaceRef(v_value_2016_, v_ref_2072_);
lean_dec(v_value_2016_);
v___x_2076_ = l_Lean_SourceInfo_fromRef(v_ref_2075_, v___x_2006_);
lean_dec(v_ref_2075_);
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_2078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17));
lean_inc_n(v_currMacroScope_2074_, 2);
lean_inc_n(v_quotContext_2073_, 2);
v___x_2080_ = l_Lean_addMacroScope(v_quotContext_2073_, v___x_2079_, v_currMacroScope_2074_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20));
lean_inc_n(v___x_2076_, 7);
v___x_2082_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2076_);
lean_ctor_set(v___x_2082_, 1, v___x_2078_);
lean_ctor_set(v___x_2082_, 2, v___x_2080_);
lean_ctor_set(v___x_2082_, 3, v___x_2081_);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22));
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23));
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2076_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25));
v___x_2089_ = l_Lean_addMacroScope(v_quotContext_2073_, v___x_2088_, v_currMacroScope_2074_);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29));
v___x_2091_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2076_);
lean_ctor_set(v___x_2091_, 1, v___x_2087_);
lean_ctor_set(v___x_2091_, 2, v___x_2089_);
lean_ctor_set(v___x_2091_, 3, v___x_2090_);
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30));
v___x_2093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2076_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_2095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2076_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = l_Lean_Syntax_node5(v___x_2076_, v___x_2084_, v___x_2086_, v___x_2091_, v___x_2093_, v___x_2070_, v___x_2095_);
v___x_2097_ = l_Lean_Syntax_node1(v___x_2076_, v___x_2083_, v___x_2096_);
v___x_2098_ = l_Lean_Syntax_node2(v___x_2076_, v___x_2077_, v___x_2082_, v___x_2097_);
v_value_2054_ = v___x_2098_;
goto v___jp_2053_;
}
}
v___jp_2025_:
{
lean_object* v_ref_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_ref_2031_ = lean_ctor_get(v___y_2030_, 5);
v___x_2032_ = l_Lean_SourceInfo_fromRef(v_ref_2031_, v___x_2006_);
v___x_2033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1));
v___x_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3));
lean_inc(v_fst_2008_);
v___x_2035_ = l_Lean_mkCIdentFrom(v_option_2007_, v_fst_2008_, v___x_2009_);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2037_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2032_, 5);
v___x_2038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2032_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
lean_ctor_set(v___x_2038_, 2, v___x_2037_);
lean_inc_ref_n(v___x_2038_, 3);
v___x_2039_ = l_Lean_Syntax_node2(v___x_2032_, v___x_2034_, v___x_2035_, v___x_2038_);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5));
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_2042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2032_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_Syntax_node3(v___x_2032_, v___x_2040_, v___x_2042_, v___x_2038_, v___y_2026_);
v___x_2044_ = l_Lean_Syntax_node3(v___x_2032_, v___x_2036_, v___x_2038_, v___x_2038_, v___x_2043_);
v___x_2045_ = l_Lean_Syntax_node2(v___x_2032_, v___x_2033_, v___x_2039_, v___x_2044_);
v___x_2046_ = lean_array_push(v_fields_2029_, v___x_2045_);
v___x_2047_ = l_Lean_NameSet_insert(v_seenFields_2028_, v_fst_2008_);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2046_);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_source_x3f_2027_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
v___jp_2053_:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lean_NameSet_contains(v_fst_2010_, v_fst_2008_);
if (v___x_2055_ == 0)
{
lean_dec_ref(v_fields_2015_);
lean_dec(v_seenFields_2014_);
lean_dec_ref(v_mkStructInst_2013_);
v___y_2026_ = v_value_2054_;
v_source_x3f_2027_ = v_fst_2011_;
v_seenFields_2028_ = v_fst_2010_;
v_fields_2029_ = v_snd_2012_;
v___y_2030_ = v___y_2022_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2056_; 
lean_dec(v_fst_2010_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
v___x_2056_ = lean_apply_9(v_mkStructInst_2013_, v_fst_2011_, v_snd_2012_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, lean_box(0));
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_a_2057_);
v___y_2026_ = v_value_2054_;
v_source_x3f_2027_ = v___x_2058_;
v_seenFields_2028_ = v_seenFields_2014_;
v_fields_2029_ = v_fields_2015_;
v___y_2030_ = v___y_2022_;
goto v___jp_2025_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_value_2054_);
lean_dec_ref(v_fields_2015_);
lean_dec(v_seenFields_2014_);
lean_dec(v_fst_2008_);
v_a_2059_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2056_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2056_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v___x_2101_ = _args[0];
lean_object* v_option_2102_ = _args[1];
lean_object* v_fst_2103_ = _args[2];
lean_object* v___x_2104_ = _args[3];
lean_object* v_fst_2105_ = _args[4];
lean_object* v_fst_2106_ = _args[5];
lean_object* v_snd_2107_ = _args[6];
lean_object* v_mkStructInst_2108_ = _args[7];
lean_object* v_seenFields_2109_ = _args[8];
lean_object* v_fields_2110_ = _args[9];
lean_object* v_value_2111_ = _args[10];
lean_object* v_____r_2112_ = _args[11];
lean_object* v___y_2113_ = _args[12];
lean_object* v___y_2114_ = _args[13];
lean_object* v___y_2115_ = _args[14];
lean_object* v___y_2116_ = _args[15];
lean_object* v___y_2117_ = _args[16];
lean_object* v___y_2118_ = _args[17];
lean_object* v___y_2119_ = _args[18];
_start:
{
uint8_t v___x_51423__boxed_2120_; uint8_t v___x_51425__boxed_2121_; lean_object* v_res_2122_; 
v___x_51423__boxed_2120_ = lean_unbox(v___x_2101_);
v___x_51425__boxed_2121_ = lean_unbox(v___x_2104_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_51423__boxed_2120_, v_option_2102_, v_fst_2103_, v___x_51425__boxed_2121_, v_fst_2105_, v_fst_2106_, v_snd_2107_, v_mkStructInst_2108_, v_seenFields_2109_, v_fields_2110_, v_value_2111_, v_____r_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v_option_2102_);
return v_res_2122_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2125_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_box(1);
v___x_2129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
v___x_2131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2128_);
return v___x_2131_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4));
v___x_2136_ = l_Lean_Expr_const___override(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(lean_object* v_structName_2143_, uint8_t v_recover_2144_, lean_object* v_as_2145_, size_t v_sz_2146_, size_t v_i_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_fst_2157_; lean_object* v_fst_2158_; lean_object* v_snd_2159_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_usize_dec_lt(v_i_2147_, v_sz_2146_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
lean_dec(v_structName_2143_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_b_2148_);
return v___x_2167_;
}
else
{
lean_object* v_snd_2168_; lean_object* v_fst_2169_; lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2287_; 
v_snd_2168_ = lean_ctor_get(v_b_2148_, 1);
lean_inc(v_snd_2168_);
v_fst_2169_ = lean_ctor_get(v_b_2148_, 0);
lean_inc(v_fst_2169_);
lean_dec_ref(v_b_2148_);
v_fst_2170_ = lean_ctor_get(v_snd_2168_, 0);
v_snd_2171_ = lean_ctor_get(v_snd_2168_, 1);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_snd_2168_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2173_ = v_snd_2168_;
v_isShared_2174_ = v_isSharedCheck_2287_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_inc(v_fst_2170_);
lean_dec(v_snd_2168_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2287_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v_a_2190_; lean_object* v___y_2194_; lean_object* v_a_2202_; lean_object* v_ref_2203_; lean_object* v_option_2204_; lean_object* v_value_2205_; uint8_t v_bool_2206_; lean_object* v_mkStructInst_2207_; lean_object* v_seenFields_2208_; lean_object* v_fields_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_a_2202_ = lean_array_uget_borrowed(v_as_2145_, v_i_2147_);
v_ref_2203_ = lean_ctor_get(v_a_2202_, 0);
v_option_2204_ = lean_ctor_get(v_a_2202_, 1);
v_value_2205_ = lean_ctor_get(v_a_2202_, 2);
v_bool_2206_ = lean_ctor_get_uint8(v_a_2202_, sizeof(void*)*3);
lean_inc(v_structName_2143_);
v_mkStructInst_2207_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed), 10, 1);
lean_closure_set(v_mkStructInst_2207_, 0, v_structName_2143_);
v_seenFields_2208_ = l_Lean_NameSet_empty;
v_fields_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v___x_2210_ = l_Lean_TSyntax_getId(v_option_2204_);
v___x_2211_ = l_Lean_Name_eraseMacroScopes(v___x_2210_);
lean_dec(v___x_2210_);
v___x_2212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7));
v___x_2213_ = lean_name_eq(v___x_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3);
lean_inc(v___x_2211_);
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2211_);
lean_inc(v_structName_2143_);
lean_inc(v_option_2204_);
v___x_2216_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2216_, 0, v_option_2204_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
lean_ctor_set(v___x_2216_, 2, v___x_2214_);
lean_ctor_set(v___x_2216_, 3, v_structName_2143_);
v___x_2217_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v___x_2216_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_fileName_2218_; lean_object* v_fileMap_2219_; lean_object* v_options_2220_; lean_object* v_currRecDepth_2221_; lean_object* v_maxRecDepth_2222_; lean_object* v_ref_2223_; lean_object* v_currNamespace_2224_; lean_object* v_openDecls_2225_; lean_object* v_initHeartbeats_2226_; lean_object* v_maxHeartbeats_2227_; lean_object* v_quotContext_2228_; lean_object* v_currMacroScope_2229_; uint8_t v_diag_2230_; lean_object* v_cancelTk_x3f_2231_; uint8_t v_suppressElabErrors_2232_; lean_object* v_inheritedTraceOptions_2233_; lean_object* v_ref_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2217_, 1);
v_fileName_2218_ = lean_ctor_get(v___y_2153_, 0);
v_fileMap_2219_ = lean_ctor_get(v___y_2153_, 1);
v_options_2220_ = lean_ctor_get(v___y_2153_, 2);
v_currRecDepth_2221_ = lean_ctor_get(v___y_2153_, 3);
v_maxRecDepth_2222_ = lean_ctor_get(v___y_2153_, 4);
v_ref_2223_ = lean_ctor_get(v___y_2153_, 5);
v_currNamespace_2224_ = lean_ctor_get(v___y_2153_, 6);
v_openDecls_2225_ = lean_ctor_get(v___y_2153_, 7);
v_initHeartbeats_2226_ = lean_ctor_get(v___y_2153_, 8);
v_maxHeartbeats_2227_ = lean_ctor_get(v___y_2153_, 9);
v_quotContext_2228_ = lean_ctor_get(v___y_2153_, 10);
v_currMacroScope_2229_ = lean_ctor_get(v___y_2153_, 11);
v_diag_2230_ = lean_ctor_get_uint8(v___y_2153_, sizeof(void*)*14);
v_cancelTk_x3f_2231_ = lean_ctor_get(v___y_2153_, 12);
v_suppressElabErrors_2232_ = lean_ctor_get_uint8(v___y_2153_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2233_ = lean_ctor_get(v___y_2153_, 13);
v_ref_2234_ = l_Lean_replaceRef(v_option_2204_, v_ref_2223_);
lean_inc_ref(v_inheritedTraceOptions_2233_);
lean_inc(v_cancelTk_x3f_2231_);
lean_inc(v_currMacroScope_2229_);
lean_inc(v_quotContext_2228_);
lean_inc(v_maxHeartbeats_2227_);
lean_inc(v_initHeartbeats_2226_);
lean_inc(v_openDecls_2225_);
lean_inc(v_currNamespace_2224_);
lean_inc(v_maxRecDepth_2222_);
lean_inc(v_currRecDepth_2221_);
lean_inc_ref(v_options_2220_);
lean_inc_ref(v_fileMap_2219_);
lean_inc_ref(v_fileName_2218_);
v___x_2235_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2235_, 0, v_fileName_2218_);
lean_ctor_set(v___x_2235_, 1, v_fileMap_2219_);
lean_ctor_set(v___x_2235_, 2, v_options_2220_);
lean_ctor_set(v___x_2235_, 3, v_currRecDepth_2221_);
lean_ctor_set(v___x_2235_, 4, v_maxRecDepth_2222_);
lean_ctor_set(v___x_2235_, 5, v_ref_2234_);
lean_ctor_set(v___x_2235_, 6, v_currNamespace_2224_);
lean_ctor_set(v___x_2235_, 7, v_openDecls_2225_);
lean_ctor_set(v___x_2235_, 8, v_initHeartbeats_2226_);
lean_ctor_set(v___x_2235_, 9, v_maxHeartbeats_2227_);
lean_ctor_set(v___x_2235_, 10, v_quotContext_2228_);
lean_ctor_set(v___x_2235_, 11, v_currMacroScope_2229_);
lean_ctor_set(v___x_2235_, 12, v_cancelTk_x3f_2231_);
lean_ctor_set(v___x_2235_, 13, v_inheritedTraceOptions_2233_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*14, v_diag_2230_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*14 + 1, v_suppressElabErrors_2232_);
lean_inc(v___x_2211_);
lean_inc(v_structName_2143_);
v___x_2236_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_2143_, v___x_2211_, v___y_2151_, v___y_2152_, v___x_2235_, v___y_2154_);
lean_dec_ref_known(v___x_2235_, 14);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
if (v_bool_2206_ == 0)
{
lean_object* v_fst_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v___x_2211_);
lean_del_object(v___x_2173_);
v_fst_2238_ = lean_ctor_get(v_a_2237_, 0);
lean_inc(v_fst_2238_);
lean_dec(v_a_2237_);
v___x_2239_ = lean_box(0);
lean_inc(v_value_2205_);
lean_inc(v_snd_2171_);
lean_inc(v_fst_2169_);
lean_inc(v_fst_2170_);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2213_, v_option_2204_, v_fst_2238_, v___x_2166_, v_fst_2170_, v_fst_2169_, v_snd_2171_, v_mkStructInst_2207_, v_seenFields_2208_, v_fields_2209_, v_value_2205_, v___x_2239_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v___y_2194_ = v___x_2240_;
goto v___jp_2193_;
}
else
{
lean_object* v_fst_2241_; lean_object* v_snd_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2268_; 
v_fst_2241_ = lean_ctor_get(v_a_2237_, 0);
v_snd_2242_ = lean_ctor_get(v_a_2237_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_a_2237_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2244_ = v_a_2237_;
v_isShared_2245_ = v_isSharedCheck_2268_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snd_2242_);
lean_inc(v_fst_2241_);
lean_dec(v_a_2237_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2268_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_snd_2242_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = l_Lean_ConstantInfo_type(v_a_2247_);
lean_dec(v_a_2247_);
v___x_2249_ = l_Lean_Expr_bindingBody_x21(v___x_2248_);
lean_dec_ref(v___x_2248_);
v___x_2250_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5);
v___x_2251_ = lean_expr_eqv(v___x_2249_, v___x_2250_);
lean_dec_ref(v___x_2249_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7);
v___x_2253_ = l_Lean_MessageData_ofName(v___x_2211_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 7);
lean_ctor_set(v___x_2244_, 1, v___x_2253_);
lean_ctor_set(v___x_2244_, 0, v___x_2252_);
v___x_2255_ = v___x_2244_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9);
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 7);
lean_ctor_set(v___x_2173_, 1, v___x_2256_);
lean_ctor_set(v___x_2173_, 0, v___x_2255_);
v___x_2258_ = v___x_2173_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_2203_, v___x_2258_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
lean_inc(v_value_2205_);
lean_inc(v_snd_2171_);
lean_inc(v_fst_2169_);
lean_inc(v_fst_2170_);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2213_, v_option_2204_, v_fst_2241_, v___x_2166_, v_fst_2170_, v_fst_2169_, v_snd_2171_, v_mkStructInst_2207_, v_seenFields_2208_, v_fields_2209_, v_value_2205_, v_a_2260_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v___y_2194_ = v___x_2261_;
goto v___jp_2193_;
}
else
{
lean_object* v_a_2262_; 
lean_dec(v_fst_2241_);
lean_dec_ref(v_mkStructInst_2207_);
v_a_2262_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2259_, 1);
v_a_2190_ = v_a_2262_;
goto v___jp_2189_;
}
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_del_object(v___x_2244_);
lean_dec(v___x_2211_);
lean_del_object(v___x_2173_);
v___x_2265_ = lean_box(0);
lean_inc(v_value_2205_);
lean_inc(v_snd_2171_);
lean_inc(v_fst_2169_);
lean_inc(v_fst_2170_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2213_, v_option_2204_, v_fst_2241_, v___x_2166_, v_fst_2170_, v_fst_2169_, v_snd_2171_, v_mkStructInst_2207_, v_seenFields_2208_, v_fields_2209_, v_value_2205_, v___x_2265_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v___y_2194_ = v___x_2266_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2267_; 
lean_del_object(v___x_2244_);
lean_dec(v_fst_2241_);
lean_dec(v___x_2211_);
lean_dec_ref(v_mkStructInst_2207_);
lean_del_object(v___x_2173_);
v_a_2267_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2246_, 1);
v_a_2190_ = v_a_2267_;
goto v___jp_2189_;
}
}
}
}
else
{
lean_object* v_a_2269_; 
lean_dec(v___x_2211_);
lean_dec_ref(v_mkStructInst_2207_);
lean_del_object(v___x_2173_);
v_a_2269_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2236_, 1);
v_a_2190_ = v_a_2269_;
goto v___jp_2189_;
}
}
else
{
lean_object* v_a_2270_; 
lean_dec(v___x_2211_);
lean_dec_ref(v_mkStructInst_2207_);
lean_del_object(v___x_2173_);
v_a_2270_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2217_, 1);
v_a_2190_ = v_a_2270_;
goto v___jp_2189_;
}
}
else
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
lean_dec(v___x_2211_);
lean_dec_ref(v_mkStructInst_2207_);
lean_del_object(v___x_2173_);
v___x_2271_ = lean_array_get_size(v_snd_2171_);
v___x_2272_ = lean_nat_dec_eq(v___x_2271_, v___x_2165_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_inc(v_fst_2169_);
lean_inc(v_structName_2143_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_2143_, v_fst_2169_, v_snd_2171_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2283_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2283_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2283_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 1);
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_box(0);
lean_inc(v_structName_2143_);
lean_inc(v_a_2202_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2202_, v_structName_2143_, v___x_2280_, v___x_2279_, v_seenFields_2208_, v_fields_2209_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v___y_2194_ = v___x_2281_;
goto v___jp_2193_;
}
}
}
else
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2273_, 1);
v_a_2190_ = v_a_2284_;
goto v___jp_2189_;
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_box(0);
lean_inc(v_snd_2171_);
lean_inc(v_fst_2170_);
lean_inc(v_fst_2169_);
lean_inc(v_structName_2143_);
lean_inc(v_a_2202_);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2202_, v_structName_2143_, v___x_2285_, v_fst_2169_, v_fst_2170_, v_snd_2171_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v___y_2194_ = v___x_2286_;
goto v___jp_2193_;
}
}
v___jp_2175_:
{
if (v___y_2177_ == 0)
{
if (v_recover_2144_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_snd_2171_);
lean_dec(v_fst_2170_);
lean_dec(v_fst_2169_);
lean_dec(v_structName_2143_);
v___x_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___y_2176_);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v___y_2176_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_dec_ref_known(v___x_2179_, 1);
v_fst_2157_ = v_fst_2169_;
v_fst_2158_ = v_fst_2170_;
v_snd_2159_ = v_snd_2171_;
goto v___jp_2156_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_snd_2171_);
lean_dec(v_fst_2170_);
lean_dec(v_fst_2169_);
lean_dec(v_structName_2143_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec(v_snd_2171_);
lean_dec(v_fst_2170_);
lean_dec(v_fst_2169_);
lean_dec(v_structName_2143_);
v___x_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___y_2176_);
return v___x_2188_;
}
}
v___jp_2189_:
{
uint8_t v___x_2191_; 
v___x_2191_ = l_Lean_Exception_isInterrupt(v_a_2190_);
if (v___x_2191_ == 0)
{
uint8_t v___x_2192_; 
lean_inc_ref(v_a_2190_);
v___x_2192_ = l_Lean_Exception_isRuntime(v_a_2190_);
v___y_2176_ = v_a_2190_;
v___y_2177_ = v___x_2192_;
goto v___jp_2175_;
}
else
{
v___y_2176_ = v_a_2190_;
v___y_2177_ = v___x_2191_;
goto v___jp_2175_;
}
}
v___jp_2193_:
{
if (lean_obj_tag(v___y_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_snd_2196_; lean_object* v_snd_2197_; lean_object* v_fst_2198_; lean_object* v_fst_2199_; lean_object* v_snd_2200_; 
lean_dec(v_snd_2171_);
lean_dec(v_fst_2170_);
lean_dec(v_fst_2169_);
v_a_2195_ = lean_ctor_get(v___y_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___y_2194_, 1);
v_snd_2196_ = lean_ctor_get(v_a_2195_, 1);
lean_inc(v_snd_2196_);
lean_dec(v_a_2195_);
v_snd_2197_ = lean_ctor_get(v_snd_2196_, 1);
lean_inc(v_snd_2197_);
v_fst_2198_ = lean_ctor_get(v_snd_2196_, 0);
lean_inc(v_fst_2198_);
lean_dec(v_snd_2196_);
v_fst_2199_ = lean_ctor_get(v_snd_2197_, 0);
lean_inc(v_fst_2199_);
v_snd_2200_ = lean_ctor_get(v_snd_2197_, 1);
lean_inc(v_snd_2200_);
lean_dec(v_snd_2197_);
v_fst_2157_ = v_fst_2198_;
v_fst_2158_ = v_fst_2199_;
v_snd_2159_ = v_snd_2200_;
goto v___jp_2156_;
}
else
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___y_2194_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___y_2194_, 1);
v_a_2190_ = v_a_2201_;
goto v___jp_2189_;
}
}
}
}
v___jp_2156_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; 
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v_fst_2158_);
lean_ctor_set(v___x_2160_, 1, v_snd_2159_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_fst_2157_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2147_, v___x_2162_);
v_i_2147_ = v___x_2163_;
v_b_2148_ = v___x_2161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___boxed(lean_object* v_structName_2288_, lean_object* v_recover_2289_, lean_object* v_as_2290_, lean_object* v_sz_2291_, lean_object* v_i_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
uint8_t v_recover_boxed_2301_; size_t v_sz_boxed_2302_; size_t v_i_boxed_2303_; lean_object* v_res_2304_; 
v_recover_boxed_2301_ = lean_unbox(v_recover_2289_);
v_sz_boxed_2302_ = lean_unbox_usize(v_sz_2291_);
lean_dec(v_sz_2291_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2292_);
lean_dec(v_i_2292_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2288_, v_recover_boxed_2301_, v_as_2290_, v_sz_boxed_2302_, v_i_boxed_2303_, v_b_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_as_2290_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0(lean_object* v_structName_2305_, uint8_t v_recover_2306_, lean_object* v_items_2307_, size_t v_sz_2308_, size_t v___x_2309_, lean_object* v___x_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_a_2319_; lean_object* v___x_2332_; 
lean_inc(v_structName_2305_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2305_, v_recover_2306_, v_items_2307_, v_sz_2308_, v___x_2309_, v___x_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v_snd_2334_; lean_object* v_fst_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2412_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v_snd_2334_ = lean_ctor_get(v_a_2333_, 1);
v_fst_2335_ = lean_ctor_get(v_a_2333_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2333_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2337_ = v_a_2333_;
v_isShared_2338_ = v_isSharedCheck_2412_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_snd_2334_);
lean_inc(v_fst_2335_);
lean_dec(v_a_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2412_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
if (lean_obj_tag(v_fst_2335_) == 0)
{
lean_object* v_snd_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2371_; 
v_snd_2339_ = lean_ctor_get(v_snd_2334_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_snd_2334_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; 
v_unused_2372_ = lean_ctor_get(v_snd_2334_, 0);
lean_dec(v_unused_2372_);
v___x_2341_ = v_snd_2334_;
v_isShared_2342_ = v_isSharedCheck_2371_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snd_2339_);
lean_dec(v_snd_2334_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2371_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_ref_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v_ref_2343_ = lean_ctor_get(v___y_2315_, 5);
v___x_2344_ = 0;
v___x_2345_ = l_Lean_SourceInfo_fromRef(v_ref_2343_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2345_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 2);
lean_ctor_set(v___x_2341_, 1, v___x_2347_);
lean_ctor_set(v___x_2341_, 0, v___x_2345_);
v___x_2349_ = v___x_2341_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2351_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2345_, 5);
v___x_2352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2345_);
lean_ctor_set(v___x_2352_, 1, v___x_2350_);
lean_ctor_set(v___x_2352_, 2, v___x_2351_);
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2355_ = l_Lean_Syntax_SepArray_ofElems(v___x_2354_, v_snd_2339_);
lean_dec(v_snd_2339_);
v___x_2356_ = l_Array_append___redArg(v___x_2351_, v___x_2355_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2345_);
lean_ctor_set(v___x_2357_, 1, v___x_2350_);
lean_ctor_set(v___x_2357_, 2, v___x_2356_);
v___x_2358_ = l_Lean_Syntax_node1(v___x_2345_, v___x_2353_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_2352_);
v___x_2360_ = l_Lean_Syntax_node1(v___x_2345_, v___x_2359_, v___x_2352_);
v___x_2361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 2);
lean_ctor_set(v___x_2337_, 1, v___x_2361_);
lean_ctor_set(v___x_2337_, 0, v___x_2345_);
v___x_2363_ = v___x_2337_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_inc(v_structName_2305_);
v___x_2364_ = l_Lean_mkCIdent(v_structName_2305_);
lean_inc_n(v___x_2345_, 2);
v___x_2365_ = l_Lean_Syntax_node2(v___x_2345_, v___x_2350_, v___x_2363_, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2345_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node6(v___x_2345_, v___x_2346_, v___x_2349_, v___x_2352_, v___x_2358_, v___x_2360_, v___x_2365_, v___x_2367_);
v_a_2319_ = v___x_2368_;
goto v___jp_2318_;
}
}
}
}
else
{
lean_object* v_snd_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2410_; 
v_snd_2373_ = lean_ctor_get(v_snd_2334_, 1);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_snd_2334_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_snd_2334_, 0);
lean_dec(v_unused_2411_);
v___x_2375_ = v_snd_2334_;
v_isShared_2376_ = v_isSharedCheck_2410_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_snd_2373_);
lean_dec(v_snd_2334_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2410_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v_val_2377_; lean_object* v_ref_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v_val_2377_ = lean_ctor_get(v_fst_2335_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v_fst_2335_, 1);
v_ref_2378_ = lean_ctor_get(v___y_2315_, 5);
v___x_2379_ = 0;
v___x_2380_ = l_Lean_SourceInfo_fromRef(v_ref_2378_, v___x_2379_);
v___x_2381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2380_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 2);
lean_ctor_set(v___x_2375_, 1, v___x_2382_);
lean_ctor_set(v___x_2375_, 0, v___x_2380_);
v___x_2384_ = v___x_2375_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
lean_inc_n(v___x_2380_, 2);
v___x_2386_ = l_Lean_Syntax_node1(v___x_2380_, v___x_2385_, v_val_2377_);
v___x_2387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 2);
lean_ctor_set(v___x_2337_, 1, v___x_2387_);
lean_ctor_set(v___x_2337_, 0, v___x_2380_);
v___x_2389_ = v___x_2337_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_inc_n(v___x_2380_, 8);
v___x_2390_ = l_Lean_Syntax_node2(v___x_2380_, v___x_2385_, v___x_2386_, v___x_2389_);
v___x_2391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2392_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_2393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2394_ = l_Lean_Syntax_SepArray_ofElems(v___x_2393_, v_snd_2373_);
lean_dec(v_snd_2373_);
v___x_2395_ = l_Array_append___redArg(v___x_2392_, v___x_2394_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2380_);
lean_ctor_set(v___x_2396_, 1, v___x_2385_);
lean_ctor_set(v___x_2396_, 2, v___x_2395_);
v___x_2397_ = l_Lean_Syntax_node1(v___x_2380_, v___x_2391_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_2399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2380_);
lean_ctor_set(v___x_2399_, 1, v___x_2385_);
lean_ctor_set(v___x_2399_, 2, v___x_2392_);
v___x_2400_ = l_Lean_Syntax_node1(v___x_2380_, v___x_2398_, v___x_2399_);
v___x_2401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_2402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2380_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
lean_inc(v_structName_2305_);
v___x_2403_ = l_Lean_mkCIdent(v_structName_2305_);
v___x_2404_ = l_Lean_Syntax_node2(v___x_2380_, v___x_2385_, v___x_2402_, v___x_2403_);
v___x_2405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2380_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_Syntax_node6(v___x_2380_, v___x_2381_, v___x_2384_, v___x_2390_, v___x_2397_, v___x_2400_, v___x_2404_, v___x_2406_);
v_a_2319_ = v___x_2407_;
goto v___jp_2318_;
}
}
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_structName_2305_);
v_a_2413_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2332_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2332_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
v___jp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2320_ = lean_box(0);
v___x_2321_ = l_Lean_mkConst(v_structName_2305_, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
v___x_2323_ = 1;
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_box(v___x_2323_);
v___x_2326_ = lean_box(v___x_2323_);
v___x_2327_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2327_, 0, v_a_2319_);
lean_closure_set(v___x_2327_, 1, v___x_2322_);
lean_closure_set(v___x_2327_, 2, v___x_2325_);
lean_closure_set(v___x_2327_, 3, v___x_2326_);
lean_closure_set(v___x_2327_, 4, v___x_2324_);
v___x_2328_ = 1;
v___x_2329_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2327_, v___x_2328_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_a_2330_, v___y_2314_);
return v___x_2331_;
}
else
{
return v___x_2329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0___boxed(lean_object* v_structName_2421_, lean_object* v_recover_2422_, lean_object* v_items_2423_, lean_object* v_sz_2424_, lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v_recover_boxed_2434_; size_t v_sz_boxed_2435_; size_t v___x_52010__boxed_2436_; lean_object* v_res_2437_; 
v_recover_boxed_2434_ = lean_unbox(v_recover_2422_);
v_sz_boxed_2435_ = lean_unbox_usize(v_sz_2424_);
lean_dec(v_sz_2424_);
v___x_52010__boxed_2436_ = lean_unbox_usize(v___x_2425_);
lean_dec(v___x_2425_);
v_res_2437_ = l_Lean_Elab_Tactic_elabConfig___lam__0(v_structName_2421_, v_recover_boxed_2434_, v_items_2423_, v_sz_boxed_2435_, v___x_52010__boxed_2436_, v___x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_items_2423_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v_env_2443_; lean_object* v___x_2444_; lean_object* v_mctx_2445_; lean_object* v_options_2446_; lean_object* v_currNamespace_2447_; lean_object* v_openDecls_2448_; lean_object* v___x_2449_; lean_object* v_ngen_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2442_ = lean_st_ref_get(v___y_2440_);
v_env_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc_ref(v_env_2443_);
lean_dec(v___x_2442_);
v___x_2444_ = lean_st_ref_get(v___y_2438_);
v_mctx_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc_ref(v_mctx_2445_);
lean_dec(v___x_2444_);
v_options_2446_ = lean_ctor_get(v___y_2439_, 2);
v_currNamespace_2447_ = lean_ctor_get(v___y_2439_, 6);
v_openDecls_2448_ = lean_ctor_get(v___y_2439_, 7);
v___x_2449_ = lean_st_ref_get(v___y_2440_);
v_ngen_2450_ = lean_ctor_get(v___x_2449_, 2);
lean_inc_ref(v_ngen_2450_);
lean_dec(v___x_2449_);
v___x_2451_ = lean_box(0);
v___x_2452_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_2448_);
lean_inc(v_currNamespace_2447_);
lean_inc_ref(v_options_2446_);
v___x_2453_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2453_, 0, v_env_2443_);
lean_ctor_set(v___x_2453_, 1, v___x_2451_);
lean_ctor_set(v___x_2453_, 2, v___x_2452_);
lean_ctor_set(v___x_2453_, 3, v_mctx_2445_);
lean_ctor_set(v___x_2453_, 4, v_options_2446_);
lean_ctor_set(v___x_2453_, 5, v_currNamespace_2447_);
lean_ctor_set(v___x_2453_, 6, v_openDecls_2448_);
lean_ctor_set(v___x_2453_, 7, v_ngen_2450_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2492_; 
v___x_2467_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2463_, v___y_2464_, v___y_2465_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2492_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2492_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_fileMap_2472_; lean_object* v_env_2473_; lean_object* v_mctx_2474_; lean_object* v_options_2475_; lean_object* v_currNamespace_2476_; lean_object* v_openDecls_2477_; lean_object* v_ngen_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2489_; 
v_fileMap_2472_ = lean_ctor_get(v___y_2464_, 1);
v_env_2473_ = lean_ctor_get(v_a_2468_, 0);
v_mctx_2474_ = lean_ctor_get(v_a_2468_, 3);
v_options_2475_ = lean_ctor_get(v_a_2468_, 4);
v_currNamespace_2476_ = lean_ctor_get(v_a_2468_, 5);
v_openDecls_2477_ = lean_ctor_get(v_a_2468_, 6);
v_ngen_2478_ = lean_ctor_get(v_a_2468_, 7);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_a_2468_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; lean_object* v_unused_2491_; 
v_unused_2490_ = lean_ctor_get(v_a_2468_, 2);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_a_2468_, 1);
lean_dec(v_unused_2491_);
v___x_2480_ = v_a_2468_;
v_isShared_2481_ = v_isSharedCheck_2489_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_ngen_2478_);
lean_inc(v_openDecls_2477_);
lean_inc(v_currNamespace_2476_);
lean_inc(v_options_2475_);
lean_inc(v_mctx_2474_);
lean_inc(v_env_2473_);
lean_dec(v_a_2468_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2489_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_box(0);
lean_inc_ref(v_fileMap_2472_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 2, v_fileMap_2472_);
lean_ctor_set(v___x_2480_, 1, v___x_2482_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_env_2473_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_fileMap_2472_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_mctx_2474_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_options_2475_);
lean_ctor_set(v_reuseFailAlloc_2488_, 5, v_currNamespace_2476_);
lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_openDecls_2477_);
lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_ngen_2478_);
v___x_2484_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2486_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2484_);
v___x_2486_ = v___x_2470_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11___boxed(lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2518_; 
v___x_2508_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2518_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2518_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2509_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2514_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed(lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(lean_object* v___x_2527_, lean_object* v_ctx_x3f_2528_, size_t v_sz_2529_, size_t v_i_2530_, lean_object* v_bs_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_lt(v_i_2530_, v_sz_2529_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
lean_dec_ref(v_ctx_x3f_2528_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_bs_2531_);
return v___x_2540_;
}
else
{
lean_object* v_assignment_2541_; lean_object* v___x_2542_; 
v_assignment_2541_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_ref(v_ctx_x3f_2528_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2536_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2542_ = lean_apply_7(v_ctx_x3f_2528_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, lean_box(0));
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_v_2544_; lean_object* v___x_2545_; lean_object* v_bs_x27_2546_; lean_object* v_a_2548_; lean_object* v_tree_2553_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v_v_2544_ = lean_array_uget(v_bs_2531_, v_i_2530_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v_bs_x27_2546_ = lean_array_uset(v_bs_2531_, v_i_2530_, v___x_2545_);
v_tree_2553_ = l_Lean_Elab_InfoTree_substitute(v_v_2544_, v_assignment_2541_);
if (lean_obj_tag(v_a_2543_) == 0)
{
v_a_2548_ = v_tree_2553_;
goto v___jp_2547_;
}
else
{
lean_object* v_val_2554_; lean_object* v___x_2555_; 
v_val_2554_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v_a_2543_, 1);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v_val_2554_);
lean_ctor_set(v___x_2555_, 1, v_tree_2553_);
v_a_2548_ = v___x_2555_;
goto v___jp_2547_;
}
v___jp_2547_:
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_add(v_i_2530_, v___x_2549_);
v___x_2551_ = lean_array_uset(v_bs_x27_2546_, v_i_2530_, v_a_2548_);
v_i_2530_ = v___x_2550_;
v_bs_2531_ = v___x_2551_;
goto _start;
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_bs_2531_);
lean_dec_ref(v_ctx_x3f_2528_);
v_a_2556_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2542_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2542_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27___boxed(lean_object* v___x_2564_, lean_object* v_ctx_x3f_2565_, lean_object* v_sz_2566_, lean_object* v_i_2567_, lean_object* v_bs_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
size_t v_sz_boxed_2576_; size_t v_i_boxed_2577_; lean_object* v_res_2578_; 
v_sz_boxed_2576_ = lean_unbox_usize(v_sz_2566_);
lean_dec(v_sz_2566_);
v_i_boxed_2577_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_res_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2564_, v_ctx_x3f_2565_, v_sz_boxed_2576_, v_i_boxed_2577_, v_bs_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___x_2564_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(lean_object* v___x_2579_, lean_object* v_ctx_x3f_2580_, lean_object* v_x_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
if (lean_obj_tag(v_x_2581_) == 0)
{
lean_object* v_cs_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2615_; 
v_cs_2589_ = lean_ctor_get(v_x_2581_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_x_2581_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2591_ = v_x_2581_;
v_isShared_2592_ = v_isSharedCheck_2615_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_cs_2589_);
lean_dec(v_x_2581_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2615_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
size_t v_sz_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v_sz_2593_ = lean_array_size(v_cs_2589_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2579_, v_ctx_x3f_2580_, v_sz_2593_, v___x_2594_, v_cs_2589_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2606_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_a_2596_);
v___x_2601_ = v___x_2591_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2591_);
v_a_2607_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2595_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2595_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_vs_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2642_; 
v_vs_2616_ = lean_ctor_get(v_x_2581_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_x_2581_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2618_ = v_x_2581_;
v_isShared_2619_ = v_isSharedCheck_2642_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_vs_2616_);
lean_dec(v_x_2581_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2642_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
size_t v_sz_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v_sz_2620_ = lean_array_size(v_vs_2616_);
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2579_, v_ctx_x3f_2580_, v_sz_2620_, v___x_2621_, v_vs_2616_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2633_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2633_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2633_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_a_2623_);
v___x_2628_ = v___x_2618_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2628_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_del_object(v___x_2618_);
v_a_2634_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2622_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2622_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(lean_object* v___x_2643_, lean_object* v_ctx_x3f_2644_, size_t v_sz_2645_, size_t v_i_2646_, lean_object* v_bs_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_usize_dec_lt(v_i_2646_, v_sz_2645_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v_ctx_x3f_2644_);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_bs_2647_);
return v___x_2656_;
}
else
{
lean_object* v_v_2657_; lean_object* v___x_2658_; 
v_v_2657_ = lean_array_uget_borrowed(v_bs_2647_, v_i_2646_);
lean_inc(v_v_2657_);
lean_inc_ref(v_ctx_x3f_2644_);
v___x_2658_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2643_, v_ctx_x3f_2644_, v_v_2657_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; lean_object* v_bs_x27_2661_; size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = lean_unsigned_to_nat(0u);
v_bs_x27_2661_ = lean_array_uset(v_bs_2647_, v_i_2646_, v___x_2660_);
v___x_2662_ = ((size_t)1ULL);
v___x_2663_ = lean_usize_add(v_i_2646_, v___x_2662_);
v___x_2664_ = lean_array_uset(v_bs_x27_2661_, v_i_2646_, v_a_2659_);
v_i_2646_ = v___x_2663_;
v_bs_2647_ = v___x_2664_;
goto _start;
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v_bs_2647_);
lean_dec_ref(v_ctx_x3f_2644_);
v_a_2666_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2658_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2658_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28___boxed(lean_object* v___x_2674_, lean_object* v_ctx_x3f_2675_, lean_object* v_sz_2676_, lean_object* v_i_2677_, lean_object* v_bs_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
size_t v_sz_boxed_2686_; size_t v_i_boxed_2687_; lean_object* v_res_2688_; 
v_sz_boxed_2686_ = lean_unbox_usize(v_sz_2676_);
lean_dec(v_sz_2676_);
v_i_boxed_2687_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_res_2688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2674_, v_ctx_x3f_2675_, v_sz_boxed_2686_, v_i_boxed_2687_, v_bs_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v___x_2674_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26___boxed(lean_object* v___x_2689_, lean_object* v_ctx_x3f_2690_, lean_object* v_x_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2689_, v_ctx_x3f_2690_, v_x_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v___x_2689_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(lean_object* v___x_2700_, lean_object* v_ctx_x3f_2701_, lean_object* v_t_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_root_2710_; lean_object* v_tail_2711_; lean_object* v_size_2712_; size_t v_shift_2713_; lean_object* v_tailOff_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2750_; 
v_root_2710_ = lean_ctor_get(v_t_2702_, 0);
v_tail_2711_ = lean_ctor_get(v_t_2702_, 1);
v_size_2712_ = lean_ctor_get(v_t_2702_, 2);
v_shift_2713_ = lean_ctor_get_usize(v_t_2702_, 4);
v_tailOff_2714_ = lean_ctor_get(v_t_2702_, 3);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_t_2702_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2716_ = v_t_2702_;
v_isShared_2717_ = v_isSharedCheck_2750_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_tailOff_2714_);
lean_inc(v_size_2712_);
lean_inc(v_tail_2711_);
lean_inc(v_root_2710_);
lean_dec(v_t_2702_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2750_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; 
lean_inc_ref(v_ctx_x3f_2701_);
v___x_2718_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2700_, v_ctx_x3f_2701_, v_root_2710_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; size_t v_sz_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v_sz_2720_ = lean_array_size(v_tail_2711_);
v___x_2721_ = ((size_t)0ULL);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2700_, v_ctx_x3f_2701_, v_sz_2720_, v___x_2721_, v_tail_2711_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2733_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2733_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2733_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 1, v_a_2723_);
lean_ctor_set(v___x_2716_, 0, v_a_2719_);
v___x_2728_ = v___x_2716_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2719_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_a_2723_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_size_2712_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_tailOff_2714_);
lean_ctor_set_usize(v_reuseFailAlloc_2732_, 4, v_shift_2713_);
v___x_2728_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2728_);
v___x_2730_ = v___x_2725_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2719_);
lean_del_object(v___x_2716_);
lean_dec(v_tailOff_2714_);
lean_dec(v_size_2712_);
v_a_2734_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2722_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2722_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_del_object(v___x_2716_);
lean_dec(v_tailOff_2714_);
lean_dec(v_size_2712_);
lean_dec_ref(v_tail_2711_);
lean_dec_ref(v_ctx_x3f_2701_);
v_a_2742_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2718_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2718_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22___boxed(lean_object* v___x_2751_, lean_object* v_ctx_x3f_2752_, lean_object* v_t_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v___x_2751_, v_ctx_x3f_2752_, v_t_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___x_2751_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(lean_object* v___y_2762_, lean_object* v_ctx_x3f_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v_a_2769_, lean_object* v_a_x3f_2770_){
_start:
{
lean_object* v___x_2772_; lean_object* v_infoState_2773_; lean_object* v_trees_2774_; lean_object* v___x_2775_; 
v___x_2772_ = lean_st_ref_get(v___y_2762_);
v_infoState_2773_ = lean_ctor_get(v___x_2772_, 7);
lean_inc_ref(v_infoState_2773_);
lean_dec(v___x_2772_);
v_trees_2774_ = lean_ctor_get(v_infoState_2773_, 2);
lean_inc_ref(v_trees_2774_);
v___x_2775_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v_infoState_2773_, v_ctx_x3f_2763_, v_trees_2774_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2762_);
lean_dec_ref(v_infoState_2773_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2814_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2814_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2814_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v_infoState_2781_; lean_object* v_env_2782_; lean_object* v_nextMacroScope_2783_; lean_object* v_ngen_2784_; lean_object* v_auxDeclNGen_2785_; lean_object* v_traceState_2786_; lean_object* v_cache_2787_; lean_object* v_messages_2788_; lean_object* v_snapshotTasks_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2813_; 
v___x_2780_ = lean_st_ref_take(v___y_2762_);
v_infoState_2781_ = lean_ctor_get(v___x_2780_, 7);
v_env_2782_ = lean_ctor_get(v___x_2780_, 0);
v_nextMacroScope_2783_ = lean_ctor_get(v___x_2780_, 1);
v_ngen_2784_ = lean_ctor_get(v___x_2780_, 2);
v_auxDeclNGen_2785_ = lean_ctor_get(v___x_2780_, 3);
v_traceState_2786_ = lean_ctor_get(v___x_2780_, 4);
v_cache_2787_ = lean_ctor_get(v___x_2780_, 5);
v_messages_2788_ = lean_ctor_get(v___x_2780_, 6);
v_snapshotTasks_2789_ = lean_ctor_get(v___x_2780_, 8);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2791_ = v___x_2780_;
v_isShared_2792_ = v_isSharedCheck_2813_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_snapshotTasks_2789_);
lean_inc(v_infoState_2781_);
lean_inc(v_messages_2788_);
lean_inc(v_cache_2787_);
lean_inc(v_traceState_2786_);
lean_inc(v_auxDeclNGen_2785_);
lean_inc(v_ngen_2784_);
lean_inc(v_nextMacroScope_2783_);
lean_inc(v_env_2782_);
lean_dec(v___x_2780_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2813_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
uint8_t v_enabled_2793_; lean_object* v_assignment_2794_; lean_object* v_lazyAssignment_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2811_; 
v_enabled_2793_ = lean_ctor_get_uint8(v_infoState_2781_, sizeof(void*)*3);
v_assignment_2794_ = lean_ctor_get(v_infoState_2781_, 0);
v_lazyAssignment_2795_ = lean_ctor_get(v_infoState_2781_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_infoState_2781_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v_infoState_2781_, 2);
lean_dec(v_unused_2812_);
v___x_2797_ = v_infoState_2781_;
v_isShared_2798_ = v_isSharedCheck_2811_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_lazyAssignment_2795_);
lean_inc(v_assignment_2794_);
lean_dec(v_infoState_2781_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2811_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = l_Lean_PersistentArray_append___redArg(v_a_2769_, v_a_2776_);
lean_dec(v_a_2776_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 2, v___x_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_assignment_2794_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_lazyAssignment_2795_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v___x_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2810_, sizeof(void*)*3, v_enabled_2793_);
v___x_2801_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2803_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 7, v___x_2801_);
v___x_2803_ = v___x_2791_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_env_2782_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_nextMacroScope_2783_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_ngen_2784_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_auxDeclNGen_2785_);
lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_traceState_2786_);
lean_ctor_set(v_reuseFailAlloc_2809_, 5, v_cache_2787_);
lean_ctor_set(v_reuseFailAlloc_2809_, 6, v_messages_2788_);
lean_ctor_set(v_reuseFailAlloc_2809_, 7, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2809_, 8, v_snapshotTasks_2789_);
v___x_2803_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2804_ = lean_st_ref_put(v___y_2762_, v___x_2803_);
v___x_2805_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2805_);
v___x_2807_ = v___x_2778_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v_a_2769_);
v_a_2815_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2775_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2775_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v___y_2823_, lean_object* v_ctx_x3f_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v_a_2830_, lean_object* v_a_x3f_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2823_, v_ctx_x3f_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v_a_2830_, v_a_x3f_2831_);
lean_dec(v_a_x3f_2831_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2823_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v_infoState_2837_; lean_object* v_trees_2838_; lean_object* v___x_2839_; lean_object* v_infoState_2840_; lean_object* v_env_2841_; lean_object* v_nextMacroScope_2842_; lean_object* v_ngen_2843_; lean_object* v_auxDeclNGen_2844_; lean_object* v_traceState_2845_; lean_object* v_cache_2846_; lean_object* v_messages_2847_; lean_object* v_snapshotTasks_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2871_; 
v___x_2836_ = lean_st_ref_get(v___y_2834_);
v_infoState_2837_ = lean_ctor_get(v___x_2836_, 7);
lean_inc_ref(v_infoState_2837_);
lean_dec(v___x_2836_);
v_trees_2838_ = lean_ctor_get(v_infoState_2837_, 2);
lean_inc_ref(v_trees_2838_);
lean_dec_ref(v_infoState_2837_);
v___x_2839_ = lean_st_ref_take(v___y_2834_);
v_infoState_2840_ = lean_ctor_get(v___x_2839_, 7);
v_env_2841_ = lean_ctor_get(v___x_2839_, 0);
v_nextMacroScope_2842_ = lean_ctor_get(v___x_2839_, 1);
v_ngen_2843_ = lean_ctor_get(v___x_2839_, 2);
v_auxDeclNGen_2844_ = lean_ctor_get(v___x_2839_, 3);
v_traceState_2845_ = lean_ctor_get(v___x_2839_, 4);
v_cache_2846_ = lean_ctor_get(v___x_2839_, 5);
v_messages_2847_ = lean_ctor_get(v___x_2839_, 6);
v_snapshotTasks_2848_ = lean_ctor_get(v___x_2839_, 8);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2850_ = v___x_2839_;
v_isShared_2851_ = v_isSharedCheck_2871_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_snapshotTasks_2848_);
lean_inc(v_infoState_2840_);
lean_inc(v_messages_2847_);
lean_inc(v_cache_2846_);
lean_inc(v_traceState_2845_);
lean_inc(v_auxDeclNGen_2844_);
lean_inc(v_ngen_2843_);
lean_inc(v_nextMacroScope_2842_);
lean_inc(v_env_2841_);
lean_dec(v___x_2839_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2871_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
uint8_t v_enabled_2852_; lean_object* v_assignment_2853_; lean_object* v_lazyAssignment_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2869_; 
v_enabled_2852_ = lean_ctor_get_uint8(v_infoState_2840_, sizeof(void*)*3);
v_assignment_2853_ = lean_ctor_get(v_infoState_2840_, 0);
v_lazyAssignment_2854_ = lean_ctor_get(v_infoState_2840_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_infoState_2840_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_infoState_2840_, 2);
lean_dec(v_unused_2870_);
v___x_2856_ = v_infoState_2840_;
v_isShared_2857_ = v_isSharedCheck_2869_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_lazyAssignment_2854_);
lean_inc(v_assignment_2853_);
lean_dec(v_infoState_2840_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2869_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2858_ = lean_unsigned_to_nat(32u);
v___x_2859_ = lean_mk_empty_array_with_capacity(v___x_2858_);
lean_dec_ref(v___x_2859_);
v___x_2860_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 2, v___x_2860_);
v___x_2862_ = v___x_2856_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_assignment_2853_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_lazyAssignment_2854_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v___x_2860_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3, v_enabled_2852_);
v___x_2862_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2864_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 7, v___x_2862_);
v___x_2864_ = v___x_2850_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_env_2841_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_nextMacroScope_2842_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_ngen_2843_);
lean_ctor_set(v_reuseFailAlloc_2867_, 3, v_auxDeclNGen_2844_);
lean_ctor_set(v_reuseFailAlloc_2867_, 4, v_traceState_2845_);
lean_ctor_set(v_reuseFailAlloc_2867_, 5, v_cache_2846_);
lean_ctor_set(v_reuseFailAlloc_2867_, 6, v_messages_2847_);
lean_ctor_set(v_reuseFailAlloc_2867_, 7, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2867_, 8, v_snapshotTasks_2848_);
v___x_2864_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_st_ref_put(v___y_2834_, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_trees_2838_);
return v___x_2866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg___boxed(lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2872_);
lean_dec(v___y_2872_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(lean_object* v_x_2875_, lean_object* v_ctx_x3f_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_infoState_2885_; uint8_t v_enabled_2886_; 
v___x_2884_ = lean_st_ref_get(v___y_2882_);
v_infoState_2885_ = lean_ctor_get(v___x_2884_, 7);
lean_inc_ref(v_infoState_2885_);
lean_dec(v___x_2884_);
v_enabled_2886_ = lean_ctor_get_uint8(v_infoState_2885_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2885_);
if (v_enabled_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec_ref(v_ctx_x3f_2876_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
lean_inc(v___y_2878_);
lean_inc_ref(v___y_2877_);
v___x_2887_ = lean_apply_7(v_x_2875_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, lean_box(0));
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; lean_object* v_a_2889_; lean_object* v_r_2890_; 
v___x_2888_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2882_);
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref(v___x_2888_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
lean_inc(v___y_2878_);
lean_inc_ref(v___y_2877_);
v_r_2890_ = lean_apply_7(v_x_2875_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, lean_box(0));
if (lean_obj_tag(v_r_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2915_; 
v_a_2891_ = lean_ctor_get(v_r_2890_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_r_2890_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2893_ = v_r_2890_;
v_isShared_2894_ = v_isSharedCheck_2915_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v_r_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2915_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
lean_inc(v_a_2891_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 1);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; 
v___x_2897_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2882_, v_ctx_x3f_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v_a_2889_, v___x_2896_);
lean_dec_ref(v___x_2896_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v___x_2897_, 0);
lean_dec(v_unused_2905_);
v___x_2899_ = v___x_2897_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_dec(v___x_2897_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v_a_2891_);
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2891_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2891_);
v_a_2906_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2897_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2897_);
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
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_a_2916_ = lean_ctor_get(v_r_2890_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v_r_2890_, 1);
v___x_2917_ = lean_box(0);
v___x_2918_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2882_, v_ctx_x3f_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v_a_2889_, v___x_2917_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v___x_2918_, 0);
lean_dec(v_unused_2926_);
v___x_2920_ = v___x_2918_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_dec(v___x_2918_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 1);
lean_ctor_set(v___x_2920_, 0, v_a_2916_);
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2916_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_a_2916_);
v_a_2927_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2918_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2918_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___boxed(lean_object* v_x_2935_, lean_object* v_ctx_x3f_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2935_, v_ctx_x3f_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(lean_object* v_x_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0));
v___x_2955_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2946_, v___f_2954_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___boxed(lean_object* v_x_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(lean_object* v_00_u03b1_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_x_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(v_00_u03b1_2975_, v_x_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
return v_res_2984_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__1(void){
_start:
{
lean_object* v_fields_2987_; lean_object* v_seenFields_2988_; lean_object* v___x_2989_; 
v_fields_2987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v_seenFields_2988_ = l_Lean_NameSet_empty;
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v_seenFields_2988_);
lean_ctor_set(v___x_2989_, 1, v_fields_2987_);
return v___x_2989_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__2(void){
_start:
{
lean_object* v___x_2990_; lean_object* v_source_x3f_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__1, &l_Lean_Elab_Tactic_elabConfig___closed__1_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__1);
v_source_x3f_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v_source_x3f_2991_);
lean_ctor_set(v___x_2992_, 1, v___x_2990_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t v_recover_2995_, lean_object* v_structName_2996_, lean_object* v_items_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; size_t v_sz_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3);
v___x_3006_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___closed__0));
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__2, &l_Lean_Elab_Tactic_elabConfig___closed__2_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__2);
v_sz_3008_ = lean_array_size(v_items_2997_);
v___x_3009_ = lean_box(v_recover_2995_);
v___x_3010_ = lean_box_usize(v_sz_3008_);
v___x_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___boxed__const__1));
v___f_3012_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabConfig___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3012_, 0, v_structName_2996_);
lean_closure_set(v___f_3012_, 1, v___x_3009_);
lean_closure_set(v___f_3012_, 2, v_items_2997_);
lean_closure_set(v___f_3012_, 3, v___x_3010_);
lean_closure_set(v___f_3012_, 4, v___x_3011_);
lean_closure_set(v___f_3012_, 5, v___x_3007_);
v___x_3013_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed), 9, 2);
lean_closure_set(v___x_3013_, 0, lean_box(0));
lean_closure_set(v___x_3013_, 1, v___f_3012_);
v___x_3014_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed), 11, 4);
lean_closure_set(v___x_3014_, 0, lean_box(0));
lean_closure_set(v___x_3014_, 1, v___x_3005_);
lean_closure_set(v___x_3014_, 2, v___x_3006_);
lean_closure_set(v___x_3014_, 3, v___x_3013_);
v___x_3015_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v___x_3014_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___boxed(lean_object* v_recover_3016_, lean_object* v_structName_3017_, lean_object* v_items_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
uint8_t v_recover_boxed_3026_; lean_object* v_res_3027_; 
v_recover_boxed_3026_ = lean_unbox(v_recover_3016_);
v_res_3027_ = l_Lean_Elab_Tactic_elabConfig(v_recover_boxed_3026_, v_structName_3017_, v_items_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(lean_object* v_00_u03b1_3028_, lean_object* v_ref_3029_, lean_object* v_msg_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_3029_, v_msg_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___boxed(lean_object* v_00_u03b1_3039_, lean_object* v_ref_3040_, lean_object* v_msg_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(v_00_u03b1_3039_, v_ref_3040_, v_msg_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v_ref_3040_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(lean_object* v_t_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_3050_, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___boxed(lean_object* v_t_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(v_t_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(lean_object* v_00_u03b1_3068_, lean_object* v_constName_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3078_, lean_object* v_constName_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(v_00_u03b1_3078_, v_constName_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(lean_object* v_00_u03b1_3088_, lean_object* v_msg_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3098_, lean_object* v_msg_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(v_00_u03b1_3098_, v_msg_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___boxed(lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___boxed(lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(lean_object* v_00_u03b1_3140_, lean_object* v_x_3141_, lean_object* v_ctx_x3f_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_3141_, v_ctx_x3f_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3151_, lean_object* v_x_3152_, lean_object* v_ctx_x3f_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(v_00_u03b1_3151_, v_x_3152_, v_ctx_x3f_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(lean_object* v_ref_3162_, lean_object* v_msgData_3163_, uint8_t v_severity_3164_, uint8_t v_isSilent_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_3162_, v_msgData_3163_, v_severity_3164_, v_isSilent_3165_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___boxed(lean_object* v_ref_3174_, lean_object* v_msgData_3175_, lean_object* v_severity_3176_, lean_object* v_isSilent_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v_severity_boxed_3185_; uint8_t v_isSilent_boxed_3186_; lean_object* v_res_3187_; 
v_severity_boxed_3185_ = lean_unbox(v_severity_3176_);
v_isSilent_boxed_3186_ = lean_unbox(v_isSilent_3177_);
v_res_3187_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(v_ref_3174_, v_msgData_3175_, v_severity_boxed_3185_, v_isSilent_boxed_3186_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v_ref_3174_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(lean_object* v_00_u03b1_3188_, lean_object* v_ref_3189_, lean_object* v_constName_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_3189_, v_constName_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b1_3199_, lean_object* v_ref_3200_, lean_object* v_constName_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(v_00_u03b1_3199_, v_ref_3200_, v_constName_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v_ref_3200_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(lean_object* v_msgData_3210_, lean_object* v_macroStack_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_3210_, v_macroStack_3211_, v___y_3216_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___boxed(lean_object* v_msgData_3220_, lean_object* v_macroStack_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(v_msgData_3220_, v_macroStack_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(lean_object* v_00_u03b1_3230_, lean_object* v_ref_3231_, lean_object* v_msg_3232_, lean_object* v_declHint_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_3231_, v_msg_3232_, v_declHint_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___boxed(lean_object* v_00_u03b1_3242_, lean_object* v_ref_3243_, lean_object* v_msg_3244_, lean_object* v_declHint_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(v_00_u03b1_3242_, v_ref_3243_, v_msg_3244_, v_declHint_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v_ref_3243_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(lean_object* v_msg_3254_, lean_object* v_declHint_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_3254_, v_declHint_3255_, v___y_3261_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___boxed(lean_object* v_msg_3264_, lean_object* v_declHint_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(v_msg_3264_, v_declHint_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
return v_res_3273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11));
v___x_3307_ = l_String_toRawSubstring_x27(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18));
v___x_3324_ = l_String_toRawSubstring_x27(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21));
v___x_3329_ = l_String_toRawSubstring_x27(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31));
v___x_3354_ = l_String_toRawSubstring_x27(v___x_3353_);
return v___x_3354_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39));
v___x_3376_ = l_String_toRawSubstring_x27(v___x_3375_);
return v___x_3376_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48));
v___x_3399_ = l_String_toRawSubstring_x27(v___x_3398_);
return v___x_3399_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3410_ = l_String_toRawSubstring_x27(v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71));
v___x_3454_ = l_String_toRawSubstring_x27(v___x_3453_);
return v___x_3454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77));
v___x_3466_ = l_String_toRawSubstring_x27(v___x_3465_);
return v___x_3466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83));
v___x_3481_ = l_String_toRawSubstring_x27(v___x_3480_);
return v___x_3481_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89));
v___x_3497_ = l_String_toRawSubstring_x27(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114));
v___x_3565_ = l_String_toRawSubstring_x27(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117));
v___x_3570_ = l_String_toRawSubstring_x27(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122));
v___x_3580_ = l_String_toRawSubstring_x27(v___x_3579_);
return v___x_3580_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128));
v___x_3594_ = l_String_toRawSubstring_x27(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131));
v___x_3599_ = l_String_toRawSubstring_x27(v___x_3598_);
return v___x_3599_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139));
v___x_3621_ = l_String_toRawSubstring_x27(v___x_3620_);
return v___x_3621_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150));
v___x_3650_ = l_String_toRawSubstring_x27(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168));
v___x_3691_ = l_String_toRawSubstring_x27(v___x_3690_);
return v___x_3691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175));
v___x_3707_ = l_String_toRawSubstring_x27(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190));
v___x_3730_ = l_String_toRawSubstring_x27(v___x_3729_);
return v___x_3730_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198));
v___x_3749_ = l_String_toRawSubstring_x27(v___x_3748_);
return v___x_3749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17));
v___x_3753_ = l_String_toRawSubstring_x27(v___x_3752_);
return v___x_3753_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210(void){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209));
v___x_3776_ = l_String_toRawSubstring_x27(v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212));
v___x_3781_ = l_String_toRawSubstring_x27(v___x_3780_);
return v___x_3781_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220));
v___x_3802_ = l_String_toRawSubstring_x27(v___x_3801_);
return v___x_3802_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224));
v___x_3809_ = l_String_toRawSubstring_x27(v___x_3808_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232));
v___x_3824_ = l_String_toRawSubstring_x27(v___x_3823_);
return v___x_3824_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238));
v___x_3836_ = l_String_toRawSubstring_x27(v___x_3835_);
return v___x_3836_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242));
v___x_3842_ = l_String_toRawSubstring_x27(v___x_3841_);
return v___x_3842_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246));
v___x_3848_ = l_String_toRawSubstring_x27(v___x_3847_);
return v___x_3848_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253));
v___x_3863_ = l_String_toRawSubstring_x27(v___x_3862_);
return v___x_3863_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15));
v___x_3869_ = l_String_toRawSubstring_x27(v___x_3868_);
return v___x_3869_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261));
v___x_3880_ = l_String_toRawSubstring_x27(v___x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(lean_object* v_doc_x3f_3895_, lean_object* v_elabName_3896_, lean_object* v_type_3897_, lean_object* v_monadName_3898_, lean_object* v_adapt_3899_, lean_object* v_recover_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v_quotContext_3903_; lean_object* v_currMacroScope_3904_; lean_object* v_ref_3905_; lean_object* v_ref_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___y_4043_; 
v_quotContext_3903_ = lean_ctor_get(v_a_3901_, 1);
v_currMacroScope_3904_ = lean_ctor_get(v_a_3901_, 2);
v_ref_3905_ = lean_ctor_get(v_a_3901_, 5);
v_ref_3906_ = l_Lean_replaceRef(v_type_3897_, v_ref_3905_);
v___x_3907_ = 0;
v___x_3908_ = l_Lean_SourceInfo_fromRef(v_ref_3906_, v___x_3907_);
lean_dec(v_ref_3906_);
v___x_3909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_3910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_3908_, 7);
v___x_3911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3908_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_3913_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_3914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3908_);
lean_ctor_set(v___x_3914_, 1, v___x_3912_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
v___x_3915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
lean_inc_ref_n(v___x_3914_, 2);
v___x_3916_ = l_Lean_Syntax_node1(v___x_3908_, v___x_3915_, v___x_3914_);
v___x_3917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_3918_ = l_Lean_Syntax_node1(v___x_3908_, v___x_3917_, v___x_3914_);
v___x_3919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_3920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3908_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
lean_inc_n(v_type_3897_, 3);
v___x_3921_ = l_Lean_Syntax_node2(v___x_3908_, v___x_3912_, v___x_3920_, v_type_3897_);
v___x_3922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_3923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3908_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = l_Lean_Syntax_node6(v___x_3908_, v___x_3909_, v___x_3911_, v___x_3914_, v___x_3916_, v___x_3918_, v___x_3921_, v___x_3923_);
v___x_3925_ = l_Lean_SourceInfo_fromRef(v_ref_3905_, v___x_3907_);
v___x_3926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1));
v___x_3927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3));
lean_inc_n(v___x_3925_, 55);
v___x_3928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3925_);
lean_ctor_set(v___x_3928_, 1, v___x_3912_);
lean_ctor_set(v___x_3928_, 2, v___x_3913_);
v___x_3929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5));
v___x_3931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3925_);
lean_ctor_set(v___x_3931_, 1, v___x_3929_);
v___x_3932_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3930_, v___x_3931_);
v___x_3933_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_3932_);
lean_inc_ref_n(v___x_3928_, 21);
v___x_3934_ = l_Lean_Syntax_node7(v___x_3925_, v___x_3927_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3933_, v___x_3928_);
v___x_3935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7));
v___x_3936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8));
v___x_3937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3925_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10));
v___x_3939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12);
v___x_3940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13));
lean_inc_n(v_currMacroScope_3904_, 9);
lean_inc_n(v_quotContext_3903_, 9);
v___x_3941_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3940_, v_currMacroScope_3904_);
v___x_3942_ = lean_box(0);
v___x_3943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3925_);
lean_ctor_set(v___x_3943_, 1, v___x_3939_);
lean_ctor_set(v___x_3943_, 2, v___x_3941_);
lean_ctor_set(v___x_3943_, 3, v___x_3942_);
lean_inc_ref(v___x_3943_);
v___x_3944_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3938_, v___x_3943_, v___x_3928_);
v___x_3945_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15));
v___x_3946_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17));
v___x_3947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
v___x_3948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3925_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19);
v___x_3950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20));
v___x_3951_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3950_, v_currMacroScope_3904_);
v___x_3952_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3925_);
lean_ctor_set(v___x_3952_, 1, v___x_3949_);
lean_ctor_set(v___x_3952_, 2, v___x_3951_);
lean_ctor_set(v___x_3952_, 3, v___x_3942_);
lean_inc_ref(v___x_3952_);
v___x_3953_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3925_);
lean_ctor_set(v___x_3954_, 1, v___x_3919_);
v___x_3955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23));
v___x_3957_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3956_, v_currMacroScope_3904_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28));
v___x_3959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3925_);
lean_ctor_set(v___x_3959_, 1, v___x_3955_);
lean_ctor_set(v___x_3959_, 2, v___x_3957_);
lean_ctor_set(v___x_3959_, 3, v___x_3958_);
lean_inc_ref_n(v___x_3954_, 2);
v___x_3960_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_3954_, v___x_3959_);
v___x_3961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_3962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3925_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
lean_inc_ref_n(v___x_3962_, 2);
lean_inc_ref_n(v___x_3948_, 2);
v___x_3963_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3946_, v___x_3948_, v___x_3953_, v___x_3960_, v___x_3928_, v___x_3962_);
v___x_3964_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_3963_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30));
v___x_3966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_3967_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32);
v___x_3968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33));
v___x_3969_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3968_, v_currMacroScope_3904_);
v___x_3970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36));
v___x_3971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3925_);
lean_ctor_set(v___x_3971_, 1, v___x_3967_);
lean_ctor_set(v___x_3971_, 2, v___x_3969_);
lean_ctor_set(v___x_3971_, 3, v___x_3970_);
v___x_3972_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v_type_3897_);
lean_inc(v___x_3972_);
v___x_3973_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_3971_, v___x_3972_);
v___x_3974_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3965_, v___x_3954_, v___x_3973_);
lean_inc(v___x_3974_);
v___x_3975_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_3974_);
lean_inc(v___x_3975_);
lean_inc(v___x_3964_);
v___x_3976_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3945_, v___x_3964_, v___x_3975_);
v___x_3977_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38));
v___x_3978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_3979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3925_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40);
v___x_3981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42));
v___x_3982_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3981_, v_currMacroScope_3904_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45));
v___x_3984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3925_);
lean_ctor_set(v___x_3984_, 1, v___x_3980_);
lean_ctor_set(v___x_3984_, 2, v___x_3982_);
lean_ctor_set(v___x_3984_, 3, v___x_3983_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47));
v___x_3986_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49);
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50));
v___x_3988_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3987_, v_currMacroScope_3904_);
v___x_3989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3925_);
lean_ctor_set(v___x_3989_, 1, v___x_3986_);
lean_ctor_set(v___x_3989_, 2, v___x_3988_);
lean_ctor_set(v___x_3989_, 3, v___x_3942_);
v___x_3990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52));
v___x_3991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_3992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3925_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54);
v___x_3994_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55));
v___x_3995_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3994_, v_currMacroScope_3904_);
v___x_3996_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3925_);
lean_ctor_set(v___x_3996_, 1, v___x_3993_);
lean_ctor_set(v___x_3996_, 2, v___x_3995_);
lean_ctor_set(v___x_3996_, 3, v___x_3942_);
lean_inc_ref(v___x_3992_);
v___x_3997_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3990_, v___x_3992_, v___x_3996_);
lean_inc_ref_n(v___x_3979_, 2);
v___x_3998_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3985_, v___x_3948_, v___x_3989_, v___x_3979_, v___x_3997_, v___x_3962_);
v___x_3999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57));
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_4001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3925_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
lean_inc_ref(v___x_4001_);
v___x_4002_ = l_Lean_Syntax_node3(v___x_3925_, v___x_3999_, v___x_4001_, v___x_4001_, v_type_3897_);
lean_inc(v___x_4002_);
v___x_4003_ = l_Lean_Syntax_node4(v___x_3925_, v___x_3912_, v___x_3998_, v_type_3897_, v___x_4002_, v___x_3952_);
v___x_4004_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_3984_, v___x_4003_);
v___x_4005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60));
v___x_4006_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4005_, v___x_3928_, v___x_3928_);
lean_inc(v___x_4006_);
v___x_4007_ = l_Lean_Syntax_node4(v___x_3925_, v___x_3977_, v___x_3979_, v___x_4004_, v___x_4006_, v___x_3928_);
lean_inc_ref(v___x_3937_);
v___x_4008_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3935_, v___x_3937_, v___x_3944_, v___x_3976_, v___x_4007_, v___x_3928_);
v___x_4009_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3926_, v___x_3934_, v___x_4008_);
v___x_4010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62));
v___x_4011_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63));
v___x_4012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_3925_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
v___x_4013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65));
v___x_4014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67));
v___x_4015_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4014_, v___x_3928_);
v___x_4016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70));
v___x_4017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72);
v___x_4018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73));
v___x_4019_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4018_, v_currMacroScope_3904_);
v___x_4020_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4020_, 0, v___x_3925_);
lean_ctor_set(v___x_4020_, 1, v___x_4017_);
lean_ctor_set(v___x_4020_, 2, v___x_4019_);
lean_ctor_set(v___x_4020_, 3, v___x_3942_);
v___x_4021_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_3943_);
v___x_4022_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4016_, v___x_4020_, v___x_4021_);
v___x_4023_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4013_, v___x_4015_, v___x_4022_);
v___x_4024_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4023_);
v___x_4025_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74));
v___x_4026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_3925_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = l_Lean_Syntax_node3(v___x_3925_, v___x_4010_, v___x_4012_, v___x_4024_, v___x_4026_);
v___x_4028_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4027_);
v___x_4029_ = l_Lean_Syntax_node7(v___x_3925_, v___x_3927_, v___x_3928_, v___x_4028_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_);
v___x_4030_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75));
v___x_4031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76));
v___x_4032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_3925_);
lean_ctor_set(v___x_4032_, 1, v___x_4030_);
v___x_4033_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78);
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79));
v___x_4035_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4034_, v_currMacroScope_3904_);
v___x_4036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4036_, 0, v___x_3925_);
lean_ctor_set(v___x_4036_, 1, v___x_4033_);
lean_ctor_set(v___x_4036_, 2, v___x_4035_);
lean_ctor_set(v___x_4036_, 3, v___x_3942_);
lean_inc_ref(v___x_4036_);
v___x_4037_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3938_, v___x_4036_, v___x_3928_);
v___x_4038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81));
v___x_4039_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4038_, v___x_3964_, v___x_3974_);
v___x_4040_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4031_, v___x_4032_, v___x_4037_, v___x_4039_, v___x_3928_);
v___x_4041_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3926_, v___x_4029_, v___x_4040_);
if (lean_obj_tag(v_doc_x3f_3895_) == 1)
{
lean_object* v_val_4373_; lean_object* v___x_4374_; 
v_val_4373_ = lean_ctor_get(v_doc_x3f_3895_, 0);
lean_inc(v_val_4373_);
lean_dec_ref_known(v_doc_x3f_3895_, 1);
v___x_4374_ = l_Array_mkArray1___redArg(v_val_4373_);
v___y_4043_ = v___x_4374_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4375_; 
lean_dec(v_doc_x3f_3895_);
v___x_4375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268));
v___y_4043_ = v___x_4375_;
goto v___jp_4042_;
}
v___jp_4042_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4044_ = l_Array_append___redArg(v___x_3913_, v___y_4043_);
lean_dec_ref(v___y_4043_);
lean_inc_n(v___x_3925_, 183);
v___x_4045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4045_, 0, v___x_3925_);
lean_ctor_set(v___x_4045_, 1, v___x_3912_);
lean_ctor_set(v___x_4045_, 2, v___x_4044_);
lean_inc_ref_n(v___x_3928_, 57);
v___x_4046_ = l_Lean_Syntax_node7(v___x_3925_, v___x_3927_, v___x_4045_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_, v___x_3928_);
v___x_4047_ = lean_box(2);
v___x_4048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82));
v___x_4049_ = lean_unsigned_to_nat(2u);
v___x_4050_ = lean_mk_empty_array_with_capacity(v___x_4049_);
v___x_4051_ = lean_array_push(v___x_4050_, v_elabName_3896_);
v___x_4052_ = lean_array_push(v___x_4051_, v___x_4048_);
v___x_4053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4047_);
lean_ctor_set(v___x_4053_, 1, v___x_3938_);
lean_ctor_set(v___x_4053_, 2, v___x_4052_);
v___x_4054_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84);
v___x_4055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85));
lean_inc_n(v_currMacroScope_3904_, 26);
lean_inc_n(v_quotContext_3903_, 26);
v___x_4056_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4055_, v_currMacroScope_3904_);
v___x_4057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88));
v___x_4058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4058_, 0, v___x_3925_);
lean_ctor_set(v___x_4058_, 1, v___x_4054_);
lean_ctor_set(v___x_4058_, 2, v___x_4056_);
lean_ctor_set(v___x_4058_, 3, v___x_4057_);
lean_inc_ref(v___x_4058_);
v___x_4059_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4058_);
v___x_4060_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90);
v___x_4061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91));
v___x_4062_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4061_, v_currMacroScope_3904_);
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96));
v___x_4064_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4064_, 0, v___x_3925_);
lean_ctor_set(v___x_4064_, 1, v___x_4060_);
lean_ctor_set(v___x_4064_, 2, v___x_4062_);
lean_ctor_set(v___x_4064_, 3, v___x_4063_);
lean_inc_ref(v___x_3954_);
v___x_4065_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_3954_, v___x_4064_);
lean_inc_ref_n(v___x_3962_, 3);
lean_inc(v___x_4059_);
lean_inc_ref_n(v___x_3948_, 2);
v___x_4066_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3946_, v___x_3948_, v___x_4059_, v___x_4065_, v___x_3928_, v___x_3962_);
v___x_4067_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4066_);
v___x_4068_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v_monadName_3898_, v___x_3972_);
v___x_4069_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3965_, v___x_3954_, v___x_4068_);
v___x_4070_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4069_);
v___x_4071_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3945_, v___x_4067_, v___x_4070_);
v___x_4072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97));
v___x_4073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98));
v___x_4074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_3925_);
lean_ctor_set(v___x_4074_, 1, v___x_4072_);
v___x_4075_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100));
v___x_4076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102));
v___x_4077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104));
v___x_4078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105));
v___x_4079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_3925_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107));
v___x_4081_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4080_, v___x_3928_);
v___x_4082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109));
v___x_4083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111));
v___x_4084_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113));
v___x_4085_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4087_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4086_, v_currMacroScope_3904_);
v___x_4088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4088_, 0, v___x_3925_);
lean_ctor_set(v___x_4088_, 1, v___x_4085_);
lean_ctor_set(v___x_4088_, 2, v___x_4087_);
lean_ctor_set(v___x_4088_, 3, v___x_3942_);
lean_inc_ref(v___x_4088_);
v___x_4089_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4084_, v___x_4088_);
lean_inc_ref_n(v___x_3979_, 5);
v___x_4090_ = l_Lean_Syntax_node5(v___x_3925_, v___x_4083_, v___x_4089_, v___x_3928_, v___x_3928_, v___x_3979_, v_recover_3900_);
v___x_4091_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4082_, v___x_4090_);
lean_inc_n(v___x_4081_, 5);
lean_inc_ref_n(v___x_4079_, 5);
v___x_4092_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4077_, v___x_4079_, v___x_3928_, v___x_4081_, v___x_4091_);
v___x_4093_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4092_, v___x_3928_);
v___x_4094_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118);
v___x_4095_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119));
v___x_4096_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4095_, v_currMacroScope_3904_);
v___x_4097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121));
v___x_4098_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4098_, 0, v___x_3925_);
lean_ctor_set(v___x_4098_, 1, v___x_4094_);
lean_ctor_set(v___x_4098_, 2, v___x_4096_);
lean_ctor_set(v___x_4098_, 3, v___x_4097_);
lean_inc_ref(v___x_4098_);
v___x_4099_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4084_, v___x_4098_);
v___x_4100_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124));
v___x_4102_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4101_, v_currMacroScope_3904_);
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127));
v___x_4104_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4104_, 0, v___x_3925_);
lean_ctor_set(v___x_4104_, 1, v___x_4100_);
lean_ctor_set(v___x_4104_, 2, v___x_4102_);
lean_ctor_set(v___x_4104_, 3, v___x_4103_);
v___x_4105_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129);
v___x_4106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130));
v___x_4107_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4106_, v_currMacroScope_3904_);
v___x_4108_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4108_, 0, v___x_3925_);
lean_ctor_set(v___x_4108_, 1, v___x_4105_);
lean_ctor_set(v___x_4108_, 2, v___x_4107_);
lean_ctor_set(v___x_4108_, 3, v___x_3942_);
lean_inc_ref(v___x_4108_);
v___x_4109_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4084_, v___x_4108_);
v___x_4110_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132);
v___x_4111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133));
v___x_4112_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4111_, v_currMacroScope_3904_);
v___x_4113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136));
v___x_4114_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4114_, 0, v___x_3925_);
lean_ctor_set(v___x_4114_, 1, v___x_4110_);
lean_ctor_set(v___x_4114_, 2, v___x_4112_);
lean_ctor_set(v___x_4114_, 3, v___x_4113_);
v___x_4115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4118_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4119_ = lean_box(0);
v___x_4120_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4119_, v_currMacroScope_3904_);
v___x_4121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4122_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4122_, 0, v___x_3925_);
lean_ctor_set(v___x_4122_, 1, v___x_4118_);
lean_ctor_set(v___x_4122_, 2, v___x_4120_);
lean_ctor_set(v___x_4122_, 3, v___x_4121_);
v___x_4123_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4117_, v___x_4122_);
v___x_4124_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4116_, v___x_3948_, v___x_4123_);
v___x_4125_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140);
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141));
v___x_4127_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4126_, v_currMacroScope_3904_);
v___x_4128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144));
v___x_4129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4129_, 0, v___x_3925_);
lean_ctor_set(v___x_4129_, 1, v___x_4125_);
lean_ctor_set(v___x_4129_, 2, v___x_4127_);
lean_ctor_set(v___x_4129_, 3, v___x_4128_);
v___x_4130_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4129_, v___x_4059_);
lean_inc(v___x_4124_);
v___x_4131_ = l_Lean_Syntax_node3(v___x_3925_, v___x_4115_, v___x_4124_, v___x_4130_, v___x_3962_);
v___x_4132_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4131_);
v___x_4133_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4114_, v___x_4132_);
v___x_4134_ = l_Lean_Syntax_node5(v___x_3925_, v___x_4083_, v___x_4109_, v___x_3928_, v___x_3928_, v___x_3979_, v___x_4133_);
v___x_4135_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4082_, v___x_4134_);
v___x_4136_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4077_, v___x_4079_, v___x_3928_, v___x_4081_, v___x_4135_);
v___x_4137_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4136_, v___x_3928_);
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146));
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147));
v___x_4140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_3925_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149));
v___x_4142_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151);
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153));
v___x_4144_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4143_, v_currMacroScope_3904_);
v___x_4145_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4145_, 0, v___x_3925_);
lean_ctor_set(v___x_4145_, 1, v___x_4142_);
lean_ctor_set(v___x_4145_, 2, v___x_4144_);
lean_ctor_set(v___x_4145_, 3, v___x_3942_);
v___x_4146_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4141_, v___x_3928_, v___x_4145_);
v___x_4147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154));
v___x_4148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_3925_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156));
v___x_4150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157));
v___x_4151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_3925_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_3924_);
lean_inc_ref(v___x_4151_);
v___x_4153_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4149_, v___x_4151_, v___x_4152_);
v___x_4154_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4153_, v___x_3928_);
lean_inc(v___x_4154_);
v___x_4155_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4154_);
v___x_4156_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4155_);
lean_inc(v___x_4156_);
lean_inc_ref_n(v___x_4148_, 3);
lean_inc_ref_n(v___x_4140_, 3);
v___x_4157_ = l_Lean_Syntax_node6(v___x_3925_, v___x_4138_, v___x_4140_, v___x_4146_, v___x_4148_, v___x_4156_, v___x_3928_, v___x_3928_);
v___x_4158_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4157_, v___x_3928_);
v___x_4159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159));
v___x_4160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160));
v___x_4161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_3925_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_3925_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4167_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169);
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170));
v___x_4169_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4168_, v_currMacroScope_3904_);
v___x_4170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174));
v___x_4171_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4171_, 0, v___x_3925_);
lean_ctor_set(v___x_4171_, 1, v___x_4167_);
lean_ctor_set(v___x_4171_, 2, v___x_4169_);
lean_ctor_set(v___x_4171_, 3, v___x_4170_);
v___x_4172_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4171_);
lean_inc_ref_n(v___x_4165_, 2);
v___x_4173_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4163_, v___x_4165_, v___x_4172_);
v___x_4174_ = l_Lean_Syntax_node3(v___x_3925_, v___x_4115_, v___x_4124_, v___x_4173_, v___x_3962_);
v___x_4175_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176);
v___x_4176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177));
v___x_4177_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4176_, v_currMacroScope_3904_);
v___x_4178_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4178_, 0, v___x_3925_);
lean_ctor_set(v___x_4178_, 1, v___x_4175_);
lean_ctor_set(v___x_4178_, 2, v___x_4177_);
lean_ctor_set(v___x_4178_, 3, v___x_3942_);
v___x_4179_ = l_Lean_Syntax_node3(v___x_3925_, v___x_4162_, v___x_4174_, v___x_3992_, v___x_4178_);
lean_inc_n(v___x_4002_, 3);
v___x_4180_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4002_);
v___x_4181_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4179_, v___x_4180_);
v___x_4182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179));
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180));
v___x_4184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_3925_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182));
v___x_4186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183));
v___x_4187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_3925_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185));
v___x_4189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187));
v___x_4190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188));
v___x_4191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_3925_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4189_, v___x_4191_);
v___x_4193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189));
v___x_4194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_3925_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4189_, v___x_4194_);
lean_inc(v___x_4195_);
v___x_4196_ = l_Lean_Syntax_node3(v___x_3925_, v___x_4188_, v___x_4192_, v___x_4002_, v___x_4195_);
lean_inc_ref_n(v___x_4187_, 2);
v___x_4197_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4185_, v___x_4187_, v___x_4196_);
lean_inc_ref_n(v___x_4184_, 2);
v___x_4198_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4182_, v___x_4184_, v___x_4197_);
v___x_4199_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4198_);
v___x_4200_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4199_, v___x_3928_);
v___x_4201_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4200_);
v___x_4202_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4201_);
lean_inc_ref_n(v___x_4074_, 2);
v___x_4203_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4159_, v___x_4161_, v___x_4181_, v___x_4074_, v___x_4202_);
v___x_4204_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4203_, v___x_3928_);
v___x_4205_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191);
v___x_4206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192));
v___x_4207_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4206_, v_currMacroScope_3904_);
v___x_4208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197));
v___x_4209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4209_, 0, v___x_3925_);
lean_ctor_set(v___x_4209_, 1, v___x_4205_);
lean_ctor_set(v___x_4209_, 2, v___x_4207_);
lean_ctor_set(v___x_4209_, 3, v___x_4208_);
v___x_4210_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199);
v___x_4211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200));
v___x_4212_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4211_, v_currMacroScope_3904_);
v___x_4213_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4213_, 0, v___x_3925_);
lean_ctor_set(v___x_4213_, 1, v___x_4210_);
lean_ctor_set(v___x_4213_, 2, v___x_4212_);
lean_ctor_set(v___x_4213_, 3, v___x_3942_);
v___x_4214_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201);
v___x_4215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202));
v___x_4216_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4215_, v_currMacroScope_3904_);
v___x_4217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204));
v___x_4218_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4218_, 0, v___x_3925_);
lean_ctor_set(v___x_4218_, 1, v___x_4214_);
lean_ctor_set(v___x_4218_, 2, v___x_4216_);
lean_ctor_set(v___x_4218_, 3, v___x_4217_);
v___x_4219_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3985_, v___x_3948_, v___x_4213_, v___x_3979_, v___x_4218_, v___x_3962_);
v___x_4220_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_4219_, v___x_4002_);
v___x_4221_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4209_, v___x_4220_);
v___x_4222_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4221_);
v___x_4223_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4222_, v___x_3928_);
v___x_4224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206));
v___x_4225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208));
v___x_4226_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210);
v___x_4227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211));
v___x_4228_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4227_, v_currMacroScope_3904_);
v___x_4229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4229_, 0, v___x_3925_);
lean_ctor_set(v___x_4229_, 1, v___x_4226_);
lean_ctor_set(v___x_4229_, 2, v___x_4228_);
lean_ctor_set(v___x_4229_, 3, v___x_3942_);
v___x_4230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213);
v___x_4231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214));
v___x_4232_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4231_, v_currMacroScope_3904_);
v___x_4233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219));
v___x_4234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4234_, 0, v___x_3925_);
lean_ctor_set(v___x_4234_, 1, v___x_4230_);
lean_ctor_set(v___x_4234_, 2, v___x_4232_);
lean_ctor_set(v___x_4234_, 3, v___x_4233_);
v___x_4235_ = l_Lean_Syntax_node3(v___x_3925_, v___x_3912_, v___x_4088_, v___x_4002_, v___x_4108_);
v___x_4236_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4234_, v___x_4235_);
v___x_4237_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4236_);
lean_inc_ref(v___x_4229_);
v___x_4238_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4225_, v___x_4229_, v___x_3928_, v___x_4165_, v___x_4237_);
v___x_4239_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4224_, v___x_4079_, v___x_3928_, v___x_4081_, v___x_4238_);
v___x_4240_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4239_, v___x_3928_);
v___x_4241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221);
v___x_4242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223));
v___x_4243_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4242_, v_currMacroScope_3904_);
v___x_4244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4244_, 0, v___x_3925_);
lean_ctor_set(v___x_4244_, 1, v___x_4241_);
lean_ctor_set(v___x_4244_, 2, v___x_4243_);
lean_ctor_set(v___x_4244_, 3, v___x_3942_);
v___x_4245_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4141_, v___x_3928_, v___x_4244_);
v___x_4246_ = l_Lean_Syntax_node6(v___x_3925_, v___x_4138_, v___x_4140_, v___x_4245_, v___x_4148_, v___x_4156_, v___x_3928_, v___x_3928_);
v___x_4247_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4246_, v___x_3928_);
v___x_4248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225);
v___x_4249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227));
v___x_4250_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4249_, v_currMacroScope_3904_);
v___x_4251_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4251_, 0, v___x_3925_);
lean_ctor_set(v___x_4251_, 1, v___x_4248_);
lean_ctor_set(v___x_4251_, 2, v___x_4250_);
lean_ctor_set(v___x_4251_, 3, v___x_3942_);
v___x_4252_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4141_, v___x_3928_, v___x_4251_);
v___x_4253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228));
v___x_4254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_3925_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4189_, v___x_4254_);
v___x_4256_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4188_, v___x_4255_);
v___x_4257_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4185_, v___x_4187_, v___x_4256_);
v___x_4258_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4182_, v___x_4184_, v___x_4257_);
v___x_4259_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4258_);
v___x_4260_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4259_, v___x_3928_);
v___x_4261_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4260_);
v___x_4262_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4261_);
v___x_4263_ = l_Lean_Syntax_node6(v___x_3925_, v___x_4138_, v___x_4140_, v___x_4252_, v___x_4148_, v___x_4262_, v___x_3928_, v___x_3928_);
v___x_4264_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4263_, v___x_3928_);
v___x_4265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230));
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231));
v___x_4267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_3925_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233);
v___x_4269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234));
v___x_4270_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4269_, v_currMacroScope_3904_);
v___x_4271_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4271_, 0, v___x_3925_);
lean_ctor_set(v___x_4271_, 1, v___x_4268_);
lean_ctor_set(v___x_4271_, 2, v___x_4270_);
lean_ctor_set(v___x_4271_, 3, v___x_3942_);
v___x_4272_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4229_);
lean_inc(v___x_4272_);
v___x_4273_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4036_, v___x_4272_);
v___x_4274_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4273_);
lean_inc_ref(v___x_4271_);
v___x_4275_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4225_, v___x_4271_, v___x_3928_, v___x_4165_, v___x_4274_);
v___x_4276_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4224_, v___x_4079_, v___x_3928_, v___x_4081_, v___x_4275_);
v___x_4277_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4276_, v___x_3928_);
v___x_4278_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4271_);
v___x_4279_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4149_, v___x_4151_, v___x_4278_);
v___x_4280_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4279_, v___x_3928_);
v___x_4281_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_4277_, v___x_4280_);
v___x_4282_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4281_);
v___x_4283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236));
v___x_4284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237));
v___x_4285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_3925_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239);
v___x_4287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240));
v___x_4288_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4287_, v_currMacroScope_3904_);
v___x_4289_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4289_, 0, v___x_3925_);
lean_ctor_set(v___x_4289_, 1, v___x_4286_);
lean_ctor_set(v___x_4289_, 2, v___x_4288_);
lean_ctor_set(v___x_4289_, 3, v___x_3942_);
v___x_4290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241));
v___x_4291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_3925_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243);
v___x_4293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244));
v___x_4294_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4293_, v_currMacroScope_3904_);
v___x_4295_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4295_, 0, v___x_3925_);
lean_ctor_set(v___x_4295_, 1, v___x_4292_);
lean_ctor_set(v___x_4295_, 2, v___x_4294_);
lean_ctor_set(v___x_4295_, 3, v___x_3942_);
lean_inc_ref_n(v___x_4295_, 2);
v___x_4296_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4084_, v___x_4295_);
v___x_4297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245));
v___x_4298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_3925_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4189_, v___x_4298_);
v___x_4300_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247);
v___x_4301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248));
v___x_4302_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4301_, v_currMacroScope_3904_);
v___x_4303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251));
v___x_4304_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4304_, 0, v___x_3925_);
lean_ctor_set(v___x_4304_, 1, v___x_4300_);
lean_ctor_set(v___x_4304_, 2, v___x_4302_);
lean_ctor_set(v___x_4304_, 3, v___x_4303_);
v___x_4305_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4304_, v___x_4272_);
v___x_4306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252));
v___x_4307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_3925_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4189_, v___x_4307_);
v___x_4309_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254);
v___x_4310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256));
v___x_4311_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4310_, v_currMacroScope_3904_);
v___x_4312_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4312_, 0, v___x_3925_);
lean_ctor_set(v___x_4312_, 1, v___x_4309_);
lean_ctor_set(v___x_4312_, 2, v___x_4311_);
lean_ctor_set(v___x_4312_, 3, v___x_3942_);
v___x_4313_ = l_Lean_Syntax_node5(v___x_3925_, v___x_4188_, v___x_4299_, v___x_4305_, v___x_4308_, v___x_4312_, v___x_4195_);
v___x_4314_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4185_, v___x_4187_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_node5(v___x_3925_, v___x_4083_, v___x_4296_, v___x_3928_, v___x_3928_, v___x_3979_, v___x_4314_);
v___x_4316_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4082_, v___x_4315_);
v___x_4317_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4077_, v___x_4079_, v___x_3928_, v___x_4081_, v___x_4316_);
v___x_4318_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4317_, v___x_3928_);
v___x_4319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257);
v___x_4320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258));
v___x_4321_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4320_, v_currMacroScope_3904_);
v___x_4322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260));
v___x_4323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4323_, 0, v___x_3925_);
lean_ctor_set(v___x_4323_, 1, v___x_4319_);
lean_ctor_set(v___x_4323_, 2, v___x_4321_);
lean_ctor_set(v___x_4323_, 3, v___x_4322_);
v___x_4324_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4141_, v___x_3928_, v___x_4323_);
v___x_4325_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262);
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263));
v___x_4327_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_4326_, v_currMacroScope_3904_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266));
v___x_4329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4329_, 0, v___x_3925_);
lean_ctor_set(v___x_4329_, 1, v___x_4325_);
lean_ctor_set(v___x_4329_, 2, v___x_4327_);
lean_ctor_set(v___x_4329_, 3, v___x_4328_);
v___x_4330_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4295_);
v___x_4331_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4329_, v___x_4330_);
v___x_4332_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4331_);
v___x_4333_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4332_, v___x_3928_);
v___x_4334_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_4333_, v___x_4154_);
v___x_4335_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4334_);
v___x_4336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267));
v___x_4337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_3925_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
v___x_4338_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4182_, v___x_4184_, v___x_4295_);
v___x_4339_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4338_);
v___x_4340_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4339_, v___x_3928_);
v___x_4341_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4340_);
v___x_4342_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4341_);
v___x_4343_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_4337_, v___x_4342_);
v___x_4344_ = l_Lean_Syntax_node6(v___x_3925_, v___x_4138_, v___x_4140_, v___x_4324_, v___x_4148_, v___x_4335_, v___x_3928_, v___x_4343_);
v___x_4345_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4344_, v___x_3928_);
v___x_4346_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_4318_, v___x_4345_);
v___x_4347_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4346_);
v___x_4348_ = l_Lean_Syntax_node5(v___x_3925_, v___x_4283_, v___x_4285_, v___x_4289_, v___x_3928_, v___x_4291_, v___x_4347_);
v___x_4349_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4348_);
v___x_4350_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4265_, v___x_4267_, v___x_4282_, v___x_4349_, v___x_3928_);
v___x_4351_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4350_, v___x_3928_);
v___x_4352_ = l_Lean_Syntax_node8(v___x_3925_, v___x_3912_, v___x_4137_, v___x_4158_, v___x_4204_, v___x_4223_, v___x_4240_, v___x_4247_, v___x_4264_, v___x_4351_);
v___x_4353_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4352_);
v___x_4354_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4073_, v___x_4074_, v___x_4353_);
v___x_4355_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3912_, v___x_4058_, v___x_4354_);
v___x_4356_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v___x_4104_, v___x_4355_);
v___x_4357_ = l_Lean_Syntax_node5(v___x_3925_, v___x_4083_, v___x_4099_, v___x_3928_, v___x_3975_, v___x_3979_, v___x_4356_);
v___x_4358_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4082_, v___x_4357_);
v___x_4359_ = l_Lean_Syntax_node4(v___x_3925_, v___x_4077_, v___x_4079_, v___x_3928_, v___x_4081_, v___x_4358_);
v___x_4360_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4359_, v___x_3928_);
v___x_4361_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4166_, v___x_4098_);
v___x_4362_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4076_, v___x_4361_, v___x_3928_);
v___x_4363_ = l_Lean_Syntax_node3(v___x_3925_, v___x_3912_, v___x_4093_, v___x_4360_, v___x_4362_);
v___x_4364_ = l_Lean_Syntax_node1(v___x_3925_, v___x_4075_, v___x_4363_);
v___x_4365_ = l_Lean_Syntax_node2(v___x_3925_, v___x_4073_, v___x_4074_, v___x_4364_);
v___x_4366_ = l_Lean_Syntax_node1(v___x_3925_, v___x_3912_, v___x_4365_);
v___x_4367_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3966_, v_adapt_3899_, v___x_4366_);
v___x_4368_ = l_Lean_Syntax_node4(v___x_3925_, v___x_3977_, v___x_3979_, v___x_4367_, v___x_4006_, v___x_3928_);
v___x_4369_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3935_, v___x_3937_, v___x_4053_, v___x_4071_, v___x_4368_, v___x_3928_);
v___x_4370_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3926_, v___x_4046_, v___x_4369_);
v___x_4371_ = l_Lean_Syntax_node3(v___x_3925_, v___x_3912_, v___x_4009_, v___x_4041_, v___x_4370_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4371_);
lean_ctor_set(v___x_4372_, 1, v_a_3902_);
return v___x_4372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___boxed(lean_object* v_doc_x3f_4376_, lean_object* v_elabName_4377_, lean_object* v_type_4378_, lean_object* v_monadName_4379_, lean_object* v_adapt_4380_, lean_object* v_recover_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v_doc_x3f_4376_, v_elabName_4377_, v_type_4378_, v_monadName_4379_, v_adapt_4380_, v_recover_4381_, v_a_4382_, v_a_4383_);
lean_dec_ref(v_a_4382_);
return v_res_4384_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0));
v___x_4429_ = l_String_toRawSubstring_x27(v___x_4428_);
return v___x_4429_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8));
v___x_4449_ = l_Lean_mkCIdent(v___x_4448_);
return v___x_4449_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11));
v___x_4454_ = l_Lean_mkCIdent(v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(lean_object* v_x_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v___x_4458_; uint8_t v___x_4459_; 
v___x_4458_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
lean_inc(v_x_4455_);
v___x_4459_ = l_Lean_Syntax_isOfKind(v_x_4455_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_dec(v_x_4455_);
v___x_4460_ = lean_box(1);
v___x_4461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
lean_ctor_set(v___x_4461_, 1, v_a_4457_);
return v___x_4461_;
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v_elabName_4465_; lean_object* v___x_4466_; lean_object* v_type_4467_; lean_object* v___y_4469_; lean_object* v___x_4522_; 
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = l_Lean_Syntax_getArg(v_x_4455_, v___x_4462_);
v___x_4464_ = lean_unsigned_to_nat(2u);
v_elabName_4465_ = l_Lean_Syntax_getArg(v_x_4455_, v___x_4464_);
v___x_4466_ = lean_unsigned_to_nat(3u);
v_type_4467_ = l_Lean_Syntax_getArg(v_x_4455_, v___x_4466_);
lean_dec(v_x_4455_);
v___x_4522_ = l_Lean_Syntax_getOptional_x3f(v___x_4463_);
lean_dec(v___x_4463_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_box(0);
v___y_4469_ = v___x_4523_;
goto v___jp_4468_;
}
else
{
lean_object* v_val_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
v_val_4524_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4522_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_val_4524_);
lean_dec(v___x_4522_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_val_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
v___y_4469_ = v___x_4529_;
goto v___jp_4468_;
}
}
}
v___jp_4468_:
{
lean_object* v_quotContext_4470_; lean_object* v_currMacroScope_4471_; lean_object* v_ref_4472_; uint8_t v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v_a_4513_; lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_quotContext_4470_ = lean_ctor_get(v_a_4456_, 1);
v_currMacroScope_4471_ = lean_ctor_get(v_a_4456_, 2);
v_ref_4472_ = lean_ctor_get(v_a_4456_, 5);
v___x_4473_ = 0;
v___x_4474_ = l_Lean_SourceInfo_fromRef(v_ref_4472_, v___x_4473_);
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_4474_, 12);
v___x_4479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4474_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
v___x_4480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4482_ = lean_box(0);
lean_inc_n(v_currMacroScope_4471_, 3);
lean_inc_n(v_quotContext_4470_, 3);
v___x_4483_ = l_Lean_addMacroScope(v_quotContext_4470_, v___x_4482_, v_currMacroScope_4471_);
v___x_4484_ = lean_box(0);
v___x_4485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4486_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4474_);
lean_ctor_set(v___x_4486_, 1, v___x_4481_);
lean_ctor_set(v___x_4486_, 2, v___x_4483_);
lean_ctor_set(v___x_4486_, 3, v___x_4485_);
v___x_4487_ = l_Lean_Syntax_node1(v___x_4474_, v___x_4480_, v___x_4486_);
v___x_4488_ = l_Lean_Syntax_node2(v___x_4474_, v___x_4477_, v___x_4479_, v___x_4487_);
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4474_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4493_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1);
v___x_4494_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2));
v___x_4495_ = l_Lean_addMacroScope(v_quotContext_4470_, v___x_4494_, v_currMacroScope_4471_);
v___x_4496_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6));
v___x_4497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4474_);
lean_ctor_set(v___x_4497_, 1, v___x_4493_);
lean_ctor_set(v___x_4497_, 2, v___x_4495_);
lean_ctor_set(v___x_4497_, 3, v___x_4496_);
v___x_4498_ = l_Lean_Syntax_node1(v___x_4474_, v___x_4492_, v___x_4497_);
v___x_4499_ = l_Lean_Syntax_node2(v___x_4474_, v___x_4489_, v___x_4491_, v___x_4498_);
v___x_4500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_4501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4474_);
lean_ctor_set(v___x_4501_, 1, v___x_4500_);
v___x_4502_ = l_Lean_Syntax_node3(v___x_4474_, v___x_4476_, v___x_4488_, v___x_4499_, v___x_4501_);
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_4504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4474_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4507_ = l_Lean_addMacroScope(v_quotContext_4470_, v___x_4506_, v_currMacroScope_4471_);
v___x_4508_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4474_);
lean_ctor_set(v___x_4508_, 1, v___x_4505_);
lean_ctor_set(v___x_4508_, 2, v___x_4507_);
lean_ctor_set(v___x_4508_, 3, v___x_4484_);
v___x_4509_ = l_Lean_Syntax_node3(v___x_4474_, v___x_4475_, v___x_4502_, v___x_4504_, v___x_4508_);
v___x_4510_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9);
v___x_4511_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12);
v___x_4512_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4469_, v_elabName_4465_, v_type_4467_, v___x_4510_, v___x_4511_, v___x_4509_, v_a_4456_, v_a_4457_);
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
v_a_4514_ = lean_ctor_get(v___x_4512_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4512_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_inc(v_a_4513_);
lean_dec(v___x_4512_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4513_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___boxed(lean_object* v_x_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(v_x_4532_, v_a_4533_, v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4542_ = lean_unsigned_to_nat(2u);
v___x_4543_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4541_, v___x_4542_, v_a_4537_, v_a_4538_, v_a_4539_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed(lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(v_a_4544_, v_a_4545_, v_a_4546_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
return v_res_4548_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed), 4, 0);
v___x_4550_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4550_, 0, v___x_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1(){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
v___x_4553_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0);
v___x_4554_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4552_, v___x_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
return v_res_4556_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2(void){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4589_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1));
v___x_4590_ = l_Lean_mkCIdent(v___x_4589_);
return v___x_4590_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4));
v___x_4598_ = l_Lean_mkCIdent(v___x_4597_);
return v___x_4598_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18));
v___x_4600_ = l_Lean_mkCIdent(v___x_4599_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(lean_object* v_x_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4604_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
lean_inc(v_x_4601_);
v___x_4605_ = l_Lean_Syntax_isOfKind(v_x_4601_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec(v_x_4601_);
v___x_4606_ = lean_box(1);
v___x_4607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
lean_ctor_set(v___x_4607_, 1, v_a_4603_);
return v___x_4607_;
}
else
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v_elabName_4611_; lean_object* v___x_4612_; lean_object* v_type_4613_; lean_object* v___y_4615_; lean_object* v___x_4629_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = l_Lean_Syntax_getArg(v_x_4601_, v___x_4608_);
v___x_4610_ = lean_unsigned_to_nat(2u);
v_elabName_4611_ = l_Lean_Syntax_getArg(v_x_4601_, v___x_4610_);
v___x_4612_ = lean_unsigned_to_nat(3u);
v_type_4613_ = l_Lean_Syntax_getArg(v_x_4601_, v___x_4612_);
lean_dec(v_x_4601_);
v___x_4629_ = l_Lean_Syntax_getOptional_x3f(v___x_4609_);
lean_dec(v___x_4609_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v___x_4630_; 
v___x_4630_ = lean_box(0);
v___y_4615_ = v___x_4630_;
goto v___jp_4614_;
}
else
{
lean_object* v_val_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
v_val_4631_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4629_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_val_4631_);
lean_dec(v___x_4629_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_val_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
v___y_4615_ = v___x_4636_;
goto v___jp_4614_;
}
}
}
v___jp_4614_:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v_a_4620_; lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
v___x_4616_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2);
v___x_4617_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5);
v___x_4618_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6);
v___x_4619_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4615_, v_elabName_4611_, v_type_4613_, v___x_4616_, v___x_4617_, v___x_4618_, v_a_4602_, v_a_4603_);
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
v_a_4621_ = lean_ctor_get(v___x_4619_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4619_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_inc(v_a_4620_);
lean_dec(v___x_4619_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4620_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___boxed(lean_object* v_x_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(v_x_4639_, v_a_4640_, v_a_4641_);
lean_dec_ref(v_a_4640_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4648_ = lean_unsigned_to_nat(2u);
v___x_4649_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4647_, v___x_4648_, v_a_4643_, v_a_4644_, v_a_4645_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed(lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(v_a_4650_, v_a_4651_, v_a_4652_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
return v_res_4654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed), 4, 0);
v___x_4656_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4656_, 0, v___x_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
v___x_4659_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0);
v___x_4660_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4658_, v___x_4659_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___boxed(lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
return v_res_4662_;
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
