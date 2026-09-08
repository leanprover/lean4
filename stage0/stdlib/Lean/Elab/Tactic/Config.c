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
lean_object* v___x_134_; lean_object* v_env_135_; lean_object* v___x_136_; lean_object* v_toCold_137_; lean_object* v_mctx_138_; lean_object* v_lctx_139_; lean_object* v_options_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_134_);
v___x_136_ = lean_st_ref_get(v___y_130_);
v_toCold_137_ = lean_ctor_get(v___y_131_, 0);
v_mctx_138_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_mctx_138_);
lean_dec(v___x_136_);
v_lctx_139_ = lean_ctor_get(v___y_129_, 2);
v_options_140_ = lean_ctor_get(v_toCold_137_, 2);
lean_inc_ref(v_options_140_);
lean_inc_ref(v_lctx_139_);
v___x_141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_141_, 0, v_env_135_);
lean_ctor_set(v___x_141_, 1, v_mctx_138_);
lean_ctor_set(v___x_141_, 2, v_lctx_139_);
lean_ctor_set(v___x_141_, 3, v_options_140_);
v___x_142_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v_msgData_128_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2___boxed(lean_object* v_msgData_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msgData_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_ref_157_; lean_object* v___x_158_; lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_ref_157_ = lean_ctor_get(v___y_154_, 2);
v___x_158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
lean_inc(v_ref_157_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_ref_157_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 1);
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg___boxed(lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__2));
v___x_179_ = lean_unsigned_to_nat(14u);
v___x_180_ = lean_unsigned_to_nat(22u);
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__1));
v___x_182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__0));
v___x_183_ = l_mkPanicMessageWithDecl(v___x_182_, v___x_181_, v___x_180_, v___x_179_, v___x_178_);
return v___x_183_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__4));
v___x_186_ = l_Lean_stringToMessageData(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__6));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__8));
v___x_192_ = l_Lean_stringToMessageData(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__10));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__14));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(lean_object* v_structName_202_, lean_object* v_fieldName_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___x_215_; lean_object* v_env_216_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___x_250_; 
v___x_215_ = lean_st_ref_get(v_a_207_);
v_env_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc_ref_n(v_env_216_, 2);
lean_dec(v___x_215_);
lean_inc(v_structName_202_);
v___x_250_ = l_Lean_isStructure(v_env_216_, v_structName_202_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_env_216_);
lean_dec(v_fieldName_203_);
v___x_251_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_252_ = l_Lean_MessageData_ofConstName(v_structName_202_, v___x_250_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_255_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
v___y_218_ = v_a_204_;
v___y_219_ = v_a_205_;
v___y_220_ = v_a_206_;
v___y_221_ = v_a_207_;
goto v___jp_217_;
}
v___jp_209_:
{
lean_object* v_projFn_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_projFn_212_ = lean_ctor_get(v___y_211_, 1);
lean_inc(v_projFn_212_);
lean_dec_ref(v___y_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___y_210_);
lean_ctor_set(v___x_213_, 1, v_projFn_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
v___jp_217_:
{
lean_object* v___x_222_; 
lean_inc(v_structName_202_);
lean_inc_ref(v_env_216_);
v___x_222_ = l_Lean_findField_x3f(v_env_216_, v_structName_202_, v_fieldName_203_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_224_; 
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
lean_inc_ref(v_env_216_);
v___x_224_ = l_Lean_getPathToBaseStructure_x3f(v_env_216_, v_val_223_, v_structName_202_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = lean_box(0);
v___x_227_ = l_List_foldl___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__0(v___x_226_, v_val_225_);
lean_dec(v_val_225_);
lean_inc(v_fieldName_203_);
v___x_228_ = l_Lean_Name_append(v___x_227_, v_fieldName_203_);
v___x_229_ = l_Lean_getFieldInfo_x3f(v_env_216_, v_val_223_, v_fieldName_203_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__3);
v___x_231_ = l_panic___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__1(v___x_230_);
v___y_210_ = v___x_228_;
v___y_211_ = v___x_231_;
goto v___jp_209_;
}
else
{
lean_object* v_val_232_; 
v_val_232_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v___x_229_, 1);
v___y_210_ = v___x_228_;
v___y_211_ = v_val_232_;
goto v___jp_209_;
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v___x_224_);
lean_dec(v_val_223_);
lean_dec_ref(v_env_216_);
v___x_233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__5);
v___x_234_ = l_Lean_MessageData_ofName(v_fieldName_203_);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__7);
v___x_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_237_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
return v___x_238_;
}
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v___x_222_);
lean_dec_ref(v_env_216_);
v___x_239_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__9);
v___x_240_ = 0;
v___x_241_ = l_Lean_MessageData_ofConstName(v_structName_202_, v___x_240_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__11);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Lean_MessageData_ofName(v_fieldName_203_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_248_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___boxed(lean_object* v_structName_265_, lean_object* v_fieldName_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_265_, v_fieldName_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(lean_object* v_00_u03b1_273_, lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___boxed(lean_object* v_00_u03b1_281_, lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2(v_00_u03b1_281_, v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__0));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__2));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(lean_object* v_fst_295_, lean_object* v_structName_296_, lean_object* v_00_u03b1_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__1);
v___x_304_ = l_Lean_MessageData_ofName(v_fst_295_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___closed__3);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = 0;
v___x_309_ = l_Lean_MessageData_ofConstName(v_structName_296_, v___x_308_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_307_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__15);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_312_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0___boxed(lean_object* v_fst_314_, lean_object* v_structName_315_, lean_object* v_00_u03b1_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_314_, v_structName_315_, v_00_u03b1_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_323_, lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_toCold_330_; lean_object* v_currRecDepth_331_; lean_object* v_ref_332_; uint8_t v_diag_333_; uint8_t v_suppressElabErrors_334_; lean_object* v_ref_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_toCold_330_ = lean_ctor_get(v___y_327_, 0);
v_currRecDepth_331_ = lean_ctor_get(v___y_327_, 1);
v_ref_332_ = lean_ctor_get(v___y_327_, 2);
v_diag_333_ = lean_ctor_get_uint8(v___y_327_, sizeof(void*)*3);
v_suppressElabErrors_334_ = lean_ctor_get_uint8(v___y_327_, sizeof(void*)*3 + 1);
v_ref_335_ = l_Lean_replaceRef(v_ref_323_, v_ref_332_);
lean_inc(v_currRecDepth_331_);
lean_inc_ref(v_toCold_330_);
v___x_336_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_336_, 0, v_toCold_330_);
lean_ctor_set(v___x_336_, 1, v_currRecDepth_331_);
lean_ctor_set(v___x_336_, 2, v_ref_335_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*3, v_diag_333_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*3 + 1, v_suppressElabErrors_334_);
v___x_337_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_324_, v___y_325_, v___y_326_, v___x_336_, v___y_328_);
lean_dec_ref_known(v___x_336_, 3);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_338_, v_msg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v_ref_338_);
return v_res_345_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_346_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
lean_ctor_set(v___x_351_, 4, v___x_349_);
lean_ctor_set(v___x_351_, 5, v___x_349_);
lean_ctor_set(v___x_351_, 6, v___x_349_);
lean_ctor_set(v___x_351_, 7, v___x_349_);
lean_ctor_set(v___x_351_, 8, v___x_349_);
lean_ctor_set(v___x_351_, 9, v___x_349_);
lean_ctor_set(v___x_351_, 10, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(32u);
v___x_353_ = lean_mk_empty_array_with_capacity(v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = ((size_t)5ULL);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_unsigned_to_nat(32u);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_360_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
lean_ctor_set(v___x_360_, 2, v___x_356_);
lean_ctor_set(v___x_360_, 3, v___x_356_);
lean_ctor_set_usize(v___x_360_, 4, v___x_355_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_box(1);
v___x_362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_361_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_386_, lean_object* v_declHint_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_env_391_; uint8_t v___x_392_; 
v___x_390_ = lean_st_ref_get(v___y_388_);
v_env_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_env_391_);
lean_dec(v___x_390_);
v___x_392_ = l_Lean_Name_isAnonymous(v_declHint_387_);
if (v___x_392_ == 0)
{
uint8_t v_isExporting_393_; 
v_isExporting_393_ = lean_ctor_get_uint8(v_env_391_, sizeof(void*)*8);
if (v_isExporting_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v_env_391_);
lean_dec(v_declHint_387_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v_msg_386_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
lean_inc_ref(v_env_391_);
v___x_395_ = l_Lean_Environment_setExporting(v_env_391_, v___x_392_);
lean_inc(v_declHint_387_);
lean_inc_ref(v___x_395_);
v___x_396_ = l_Lean_Environment_contains(v___x_395_, v_declHint_387_, v_isExporting_393_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v___x_395_);
lean_dec_ref(v_env_391_);
lean_dec(v_declHint_387_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_msg_386_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_c_403_; lean_object* v___x_404_; 
v___x_398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_400_ = l_Lean_Options_empty;
v___x_401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_401_, 0, v___x_395_);
lean_ctor_set(v___x_401_, 1, v___x_398_);
lean_ctor_set(v___x_401_, 2, v___x_399_);
lean_ctor_set(v___x_401_, 3, v___x_400_);
lean_inc(v_declHint_387_);
v___x_402_ = l_Lean_MessageData_ofConstName(v_declHint_387_, v___x_392_);
v_c_403_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_403_, 0, v___x_401_);
lean_ctor_set(v_c_403_, 1, v___x_402_);
v___x_404_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_391_, v_declHint_387_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref(v_env_391_);
lean_dec(v_declHint_387_);
v___x_405_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_c_403_);
v___x_407_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_MessageData_note(v___x_408_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v_msg_386_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_447_; 
v_val_412_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_447_ == 0)
{
v___x_414_ = v___x_404_;
v_isShared_415_ = v_isSharedCheck_447_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v___x_404_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_447_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_mod_419_; uint8_t v___x_420_; 
v___x_416_ = lean_box(0);
v___x_417_ = l_Lean_Environment_header(v_env_391_);
lean_dec_ref(v_env_391_);
v___x_418_ = l_Lean_EnvironmentHeader_moduleNames(v___x_417_);
v_mod_419_ = lean_array_get(v___x_416_, v___x_418_, v_val_412_);
lean_dec(v_val_412_);
lean_dec_ref(v___x_418_);
v___x_420_ = l_Lean_isPrivateName(v_declHint_387_);
lean_dec(v_declHint_387_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_421_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_c_403_);
v___x_423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_MessageData_ofName(v_mod_419_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_MessageData_note(v___x_428_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v_msg_386_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
lean_ctor_set(v___x_414_, 0, v___x_430_);
v___x_432_ = v___x_414_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_434_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_c_403_);
v___x_436_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_MessageData_ofName(v_mod_419_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_MessageData_note(v___x_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v_msg_386_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
lean_ctor_set(v___x_414_, 0, v___x_443_);
v___x_445_ = v___x_414_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_448_; 
lean_dec_ref(v_env_391_);
lean_dec(v_declHint_387_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_msg_386_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_449_, lean_object* v_declHint_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_449_, v_declHint_450_, v___y_451_);
lean_dec(v___y_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_454_, lean_object* v_declHint_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
v___x_461_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_454_, v_declHint_455_, v___y_459_);
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = l_Lean_unknownIdentifierMessageTag;
v___x_467_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_472_, lean_object* v_declHint_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_472_, v_declHint_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_480_, lean_object* v_msg_481_, lean_object* v_declHint_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; lean_object* v_a_489_; lean_object* v___x_490_; 
v___x_488_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_481_, v_declHint_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_480_, v_a_489_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_491_, lean_object* v_msg_492_, lean_object* v_declHint_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_491_, v_msg_492_, v_declHint_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v_ref_491_);
return v_res_499_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_503_, lean_object* v_constName_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_510_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_511_ = 0;
lean_inc(v_constName_504_);
v___x_512_ = l_Lean_MessageData_ofConstName(v_constName_504_, v___x_511_);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_503_, v___x_515_, v_constName_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_517_, lean_object* v_constName_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_517_, v_constName_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v_ref_517_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(lean_object* v_constName_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_ref_531_; lean_object* v___x_532_; 
v_ref_531_ = lean_ctor_get(v___y_528_, 2);
v___x_532_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_531_, v_constName_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg___boxed(lean_object* v_constName_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(lean_object* v_constName_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; lean_object* v_env_547_; uint8_t v___x_548_; lean_object* v___x_549_; 
v___x_546_ = lean_st_ref_get(v___y_544_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_546_);
v___x_548_ = 0;
lean_inc(v_constName_540_);
v___x_549_ = l_Lean_Environment_find_x3f(v_env_547_, v_constName_540_, v___x_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_550_;
}
else
{
lean_object* v_val_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_constName_540_);
v_val_551_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_549_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_val_551_);
lean_dec(v___x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 0);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_val_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0___boxed(lean_object* v_constName_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_constName_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_565_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(lean_object* v_structName_569_, lean_object* v_field_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
if (lean_obj_tag(v_field_570_) == 1)
{
lean_object* v_pre_576_; 
v_pre_576_ = lean_ctor_get(v_field_570_, 0);
if (lean_obj_tag(v_pre_576_) == 0)
{
lean_object* v_str_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_str_577_ = lean_ctor_get(v_field_570_, 1);
lean_inc_ref(v_str_577_);
lean_dec_ref_known(v_field_570_, 2);
v___x_578_ = lean_box(0);
v___x_579_ = l_Lean_Name_str___override(v___x_578_, v_str_577_);
v___x_580_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_569_, v___x_579_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_580_;
}
else
{
lean_object* v_str_581_; lean_object* v___x_582_; 
lean_inc(v_pre_576_);
v_str_581_ = lean_ctor_get(v_field_570_, 1);
lean_inc_ref(v_str_581_);
lean_dec_ref_known(v_field_570_, 2);
lean_inc(v_structName_569_);
v___x_582_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_569_, v_pre_576_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v_fst_584_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_fst_584_);
v_snd_585_ = lean_ctor_get(v_a_583_, 1);
lean_inc(v_snd_585_);
lean_dec(v_a_583_);
v___x_586_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_snd_585_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = l_Lean_ConstantInfo_type(v_a_587_);
lean_dec(v_a_587_);
v___x_589_ = l_Lean_Expr_getForallBody(v___x_588_);
lean_dec_ref(v___x_588_);
if (lean_obj_tag(v___x_589_) == 4)
{
lean_object* v_declName_590_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___x_617_; lean_object* v_env_618_; uint8_t v___x_619_; 
v_declName_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_n(v_declName_590_, 2);
lean_dec_ref_known(v___x_589_, 2);
v___x_617_ = lean_st_ref_get(v_a_574_);
v_env_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_ref(v_env_618_);
lean_dec(v___x_617_);
v___x_619_ = l_Lean_isStructure(v_env_618_, v_declName_590_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_inc(v_fst_584_);
v___x_620_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_584_, v_structName_569_, lean_box(0), v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec_ref_known(v___x_620_, 1);
v___y_592_ = v_a_571_;
v___y_593_ = v_a_572_;
v___y_594_ = v_a_573_;
v___y_595_ = v_a_574_;
goto v___jp_591_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_declName_590_);
lean_dec(v_fst_584_);
lean_dec_ref(v_str_581_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_dec(v_structName_569_);
v___y_592_ = v_a_571_;
v___y_593_ = v_a_572_;
v___y_594_ = v_a_573_;
v___y_595_ = v_a_574_;
goto v___jp_591_;
}
v___jp_591_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_box(0);
v___x_597_ = l_Lean_Name_str___override(v___x_596_, v_str_581_);
v___x_598_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_declName_590_, v___x_597_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_616_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_616_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_616_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_616_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_615_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
v_snd_604_ = lean_ctor_get(v_a_599_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_a_599_);
if (v_isSharedCheck_615_ == 0)
{
v___x_606_ = v_a_599_;
v_isShared_607_ = v_isSharedCheck_615_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_inc(v_fst_603_);
lean_dec(v_a_599_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_615_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_Name_append(v_fst_584_, v_fst_603_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_snd_604_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_610_);
v___x_612_ = v___x_601_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_dec(v_fst_584_);
return v___x_598_;
}
}
}
else
{
lean_object* v___x_629_; 
lean_dec_ref(v___x_589_);
lean_dec_ref(v_str_581_);
v___x_629_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_584_, v_structName_569_, lean_box(0), v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_629_;
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_fst_584_);
lean_dec_ref(v_str_581_);
lean_dec(v_structName_569_);
v_a_630_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_586_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_586_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_dec_ref(v_str_581_);
lean_dec(v_structName_569_);
return v___x_582_;
}
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_field_570_);
lean_dec(v_structName_569_);
v___x_638_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1);
v___x_639_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_638_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___boxed(lean_object* v_structName_640_, lean_object* v_field_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_640_, v_field_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(lean_object* v_00_u03b1_648_, lean_object* v_constName_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___boxed(lean_object* v_00_u03b1_656_, lean_object* v_constName_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(v_00_u03b1_656_, v_constName_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_664_, lean_object* v_ref_665_, lean_object* v_constName_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_665_, v_constName_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_673_, lean_object* v_ref_674_, lean_object* v_constName_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(v_00_u03b1_673_, v_ref_674_, v_constName_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v_ref_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_682_, lean_object* v_ref_683_, lean_object* v_msg_684_, lean_object* v_declHint_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_683_, v_msg_684_, v_declHint_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_692_, lean_object* v_ref_693_, lean_object* v_msg_694_, lean_object* v_declHint_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_692_, v_ref_693_, v_msg_694_, v_declHint_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v_ref_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_702_, lean_object* v_declHint_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_702_, v_declHint_703_, v___y_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_710_, lean_object* v_declHint_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_710_, v_declHint_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_718_, lean_object* v_ref_719_, lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_719_, v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_727_, lean_object* v_ref_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_727_, v_ref_728_, v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_ref_728_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(lean_object* v_e_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = l_Lean_Expr_hasMVar(v_e_736_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_e_736_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v_mctx_742_; lean_object* v___x_743_; lean_object* v_fst_744_; lean_object* v_snd_745_; lean_object* v___x_746_; lean_object* v_cache_747_; lean_object* v_zetaDeltaFVarIds_748_; lean_object* v_postponed_749_; lean_object* v_diag_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_759_; 
v___x_741_ = lean_st_ref_get(v___y_737_);
v_mctx_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc_ref(v_mctx_742_);
lean_dec(v___x_741_);
v___x_743_ = l_Lean_instantiateMVarsCore(v_mctx_742_, v_e_736_);
v_fst_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_fst_744_);
v_snd_745_ = lean_ctor_get(v___x_743_, 1);
lean_inc(v_snd_745_);
lean_dec_ref(v___x_743_);
v___x_746_ = lean_st_ref_take(v___y_737_);
v_cache_747_ = lean_ctor_get(v___x_746_, 1);
v_zetaDeltaFVarIds_748_ = lean_ctor_get(v___x_746_, 2);
v_postponed_749_ = lean_ctor_get(v___x_746_, 3);
v_diag_750_ = lean_ctor_get(v___x_746_, 4);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_760_);
v___x_752_ = v___x_746_;
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_diag_750_);
lean_inc(v_postponed_749_);
lean_inc(v_zetaDeltaFVarIds_748_);
lean_inc(v_cache_747_);
lean_dec(v___x_746_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v_snd_745_);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_snd_745_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_cache_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_zetaDeltaFVarIds_748_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_postponed_749_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_diag_750_);
v___x_755_ = v_reuseFailAlloc_758_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_st_ref_put(v___y_737_, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_fst_744_);
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg___boxed(lean_object* v_e_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_761_, v___y_762_);
lean_dec(v___y_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(lean_object* v_e_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_765_, v___y_769_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___boxed(lean_object* v_e_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(v_e_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(lean_object* v_x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
v___x_791_ = lean_apply_7(v_x_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, lean_box(0));
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed(lean_object* v_x_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(v_x_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(lean_object* v_lctx_801_, lean_object* v_localInsts_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___f_811_; lean_object* v___x_812_; 
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
v___f_811_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_811_, 0, v_x_803_);
lean_closure_set(v___f_811_, 1, v___y_804_);
lean_closure_set(v___f_811_, 2, v___y_805_);
v___x_812_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_801_, v_localInsts_802_, v___f_811_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_812_) == 0)
{
return v___x_812_;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___boxed(lean_object* v_lctx_821_, lean_object* v_localInsts_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_821_, v_localInsts_822_, v_x_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(lean_object* v_00_u03b1_832_, lean_object* v_lctx_833_, lean_object* v_localInsts_834_, lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_833_, v_localInsts_834_, v_x_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed(lean_object* v_00_u03b1_844_, lean_object* v_lctx_845_, lean_object* v_localInsts_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(v_00_u03b1_844_, v_lctx_845_, v_localInsts_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl(lean_box(0), v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_864_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_864_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg___boxed(lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(lean_object* v_00_u03b1_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___boxed(lean_object* v_00_u03b1_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(v_00_u03b1_900_, v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_909_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6(void){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Array_mkArray0(lean_box(0));
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(lean_object* v_structName_938_, lean_object* v_source_x3f_939_, lean_object* v_fields_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
if (lean_obj_tag(v_source_x3f_939_) == 0)
{
lean_object* v_ref_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_ref_948_ = lean_ctor_get(v___y_945_, 2);
v___x_949_ = 0;
v___x_950_ = l_Lean_SourceInfo_fromRef(v_ref_948_, v___x_949_);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_950_, 8);
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_955_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_956_, 0, v___x_950_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_959_ = l_Lean_Syntax_SepArray_ofElems(v___x_958_, v_fields_940_);
v___x_960_ = l_Array_append___redArg(v___x_955_, v___x_959_);
lean_dec_ref(v___x_959_);
v___x_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_950_);
lean_ctor_set(v___x_961_, 1, v___x_954_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
v___x_962_ = l_Lean_Syntax_node1(v___x_950_, v___x_957_, v___x_961_);
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_956_);
v___x_964_ = l_Lean_Syntax_node1(v___x_950_, v___x_963_, v___x_956_);
v___x_965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_950_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_mkCIdent(v_structName_938_);
v___x_968_ = l_Lean_Syntax_node2(v___x_950_, v___x_954_, v___x_966_, v___x_967_);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_950_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_Syntax_node6(v___x_950_, v___x_951_, v___x_953_, v___x_956_, v___x_962_, v___x_964_, v___x_968_, v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
else
{
lean_object* v_val_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1008_; 
v_val_973_ = lean_ctor_get(v_source_x3f_939_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_source_x3f_939_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_975_ = v_source_x3f_939_;
v_isShared_976_ = v_isSharedCheck_1008_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_val_973_);
lean_dec(v_source_x3f_939_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1008_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_ref_977_; uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v_ref_977_ = lean_ctor_get(v___y_945_, 2);
v___x_978_ = 0;
v___x_979_ = l_Lean_SourceInfo_fromRef(v_ref_977_, v___x_978_);
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_979_, 11);
v___x_982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_979_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_984_ = l_Lean_Syntax_node1(v___x_979_, v___x_983_, v_val_973_);
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_979_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_Syntax_node2(v___x_979_, v___x_983_, v___x_984_, v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_991_ = l_Lean_Syntax_SepArray_ofElems(v___x_990_, v_fields_940_);
v___x_992_ = l_Array_append___redArg(v___x_989_, v___x_991_);
lean_dec_ref(v___x_991_);
v___x_993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_993_, 0, v___x_979_);
lean_ctor_set(v___x_993_, 1, v___x_983_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
v___x_994_ = l_Lean_Syntax_node1(v___x_979_, v___x_988_, v___x_993_);
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v___x_979_);
lean_ctor_set(v___x_996_, 1, v___x_983_);
lean_ctor_set(v___x_996_, 2, v___x_989_);
v___x_997_ = l_Lean_Syntax_node1(v___x_979_, v___x_995_, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_979_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_mkCIdent(v_structName_938_);
v___x_1001_ = l_Lean_Syntax_node2(v___x_979_, v___x_983_, v___x_999_, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_979_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node6(v___x_979_, v___x_980_, v___x_982_, v___x_987_, v___x_994_, v___x_997_, v___x_1001_, v___x_1003_);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
lean_ctor_set(v___x_975_, 0, v___x_1004_);
v___x_1006_ = v___x_975_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed(lean_object* v_structName_1009_, lean_object* v_source_x3f_1010_, lean_object* v_fields_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_1009_, v_source_x3f_1010_, v_fields_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_fields_1011_);
return v_res_1019_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_1037_ = l_String_toRawSubstring_x27(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(lean_object* v_a_1087_, lean_object* v_structName_1088_, lean_object* v_____r_1089_, lean_object* v_source_x3f_1090_, lean_object* v_seenFields_1091_, lean_object* v_fields_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_toCold_1100_; lean_object* v_value_1101_; lean_object* v_ref_1102_; lean_object* v_quotContext_1103_; lean_object* v_currMacroScope_1104_; lean_object* v_ref_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_toCold_1100_ = lean_ctor_get(v___y_1097_, 0);
v_value_1101_ = lean_ctor_get(v_a_1087_, 2);
lean_inc(v_value_1101_);
lean_dec_ref(v_a_1087_);
v_ref_1102_ = lean_ctor_get(v___y_1097_, 2);
v_quotContext_1103_ = lean_ctor_get(v_toCold_1100_, 8);
v_currMacroScope_1104_ = lean_ctor_get(v_toCold_1100_, 9);
v_ref_1105_ = l_Lean_replaceRef(v_value_1101_, v_ref_1102_);
v___x_1106_ = 0;
v___x_1107_ = l_Lean_SourceInfo_fromRef(v_ref_1105_, v___x_1106_);
lean_dec(v_ref_1105_);
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1));
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_1107_, 8);
v___x_1111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1107_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_1113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_1114_ = lean_box(0);
lean_inc(v_currMacroScope_1104_);
lean_inc(v_quotContext_1103_);
v___x_1115_ = l_Lean_addMacroScope(v_quotContext_1103_, v___x_1114_, v_currMacroScope_1104_);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_1117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1107_);
lean_ctor_set(v___x_1117_, 1, v___x_1113_);
lean_ctor_set(v___x_1117_, 2, v___x_1115_);
lean_ctor_set(v___x_1117_, 3, v___x_1116_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1107_, v___x_1112_, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1109_, v___x_1111_, v___x_1118_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1107_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_1123_ = l_Lean_mkCIdent(v_structName_1088_);
lean_inc(v___x_1123_);
v___x_1124_ = l_Lean_Syntax_node1(v___x_1107_, v___x_1122_, v___x_1123_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_1126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1107_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_inc_ref(v___x_1121_);
v___x_1127_ = l_Lean_Syntax_node5(v___x_1107_, v___x_1108_, v___x_1119_, v_value_1101_, v___x_1121_, v___x_1124_, v___x_1126_);
if (lean_obj_tag(v_source_x3f_1090_) == 1)
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1159_; 
v_val_1128_ = lean_ctor_get(v_source_x3f_1090_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_source_x3f_1090_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1130_ = v_source_x3f_1090_;
v_isShared_1131_ = v_isSharedCheck_1159_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v_source_x3f_1090_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1159_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_1133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_1107_, 10);
v___x_1134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1107_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27));
v___x_1136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1107_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_node3(v___x_1107_, v___x_1122_, v___x_1127_, v___x_1136_, v_val_1128_);
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1107_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1122_, v___x_1137_, v___x_1139_);
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_1142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_1143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1107_);
lean_ctor_set(v___x_1143_, 1, v___x_1122_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
lean_inc_ref(v___x_1143_);
v___x_1144_ = l_Lean_Syntax_node1(v___x_1107_, v___x_1141_, v___x_1143_);
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1146_ = l_Lean_Syntax_node1(v___x_1107_, v___x_1145_, v___x_1143_);
v___x_1147_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1122_, v___x_1121_, v___x_1123_);
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1107_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_Syntax_node6(v___x_1107_, v___x_1132_, v___x_1134_, v___x_1140_, v___x_1144_, v___x_1146_, v___x_1147_, v___x_1149_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1150_);
v___x_1152_ = v___x_1130_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_seenFields_1091_);
lean_ctor_set(v___x_1154_, 1, v_fields_1092_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1153_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v___x_1123_);
lean_dec_ref_known(v___x_1121_, 2);
lean_dec(v___x_1107_);
lean_dec(v_source_x3f_1090_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1127_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_seenFields_1091_);
lean_ctor_set(v___x_1162_, 1, v_fields_1092_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1161_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___boxed(lean_object* v_a_1166_, lean_object* v_structName_1167_, lean_object* v_____r_1168_, lean_object* v_source_x3f_1169_, lean_object* v_seenFields_1170_, lean_object* v_fields_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_1166_, v_structName_1167_, v_____r_1168_, v_source_x3f_1169_, v_seenFields_1170_, v_fields_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(lean_object* v_opts_1180_, lean_object* v_opt_1181_){
_start:
{
lean_object* v_name_1182_; lean_object* v_defValue_1183_; lean_object* v_map_1184_; lean_object* v___x_1185_; 
v_name_1182_ = lean_ctor_get(v_opt_1181_, 0);
v_defValue_1183_ = lean_ctor_get(v_opt_1181_, 1);
v_map_1184_ = lean_ctor_get(v_opts_1180_, 0);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1184_, v_name_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_unbox(v_defValue_1183_);
return v___x_1186_;
}
else
{
lean_object* v_val_1187_; 
v_val_1187_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v___x_1185_, 1);
if (lean_obj_tag(v_val_1187_) == 1)
{
uint8_t v_v_1188_; 
v_v_1188_ = lean_ctor_get_uint8(v_val_1187_, 0);
lean_dec_ref_known(v_val_1187_, 0);
return v_v_1188_;
}
else
{
uint8_t v___x_1189_; 
lean_dec(v_val_1187_);
v___x_1189_ = lean_unbox(v_defValue_1183_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_opts_1190_, lean_object* v_opt_1191_){
_start:
{
uint8_t v_res_1192_; lean_object* v_r_1193_; 
v_res_1192_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_opts_1190_, v_opt_1191_);
lean_dec_ref(v_opt_1191_);
lean_dec_ref(v_opts_1190_);
v_r_1193_ = lean_box(v_res_1192_);
return v_r_1193_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_box(1);
v___x_1195_ = l_Lean_MessageData_ofFormat(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2));
v___x_1200_ = l_Lean_MessageData_ofFormat(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
return v_x_1201_;
}
else
{
lean_object* v_head_1203_; lean_object* v_tail_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1226_; 
v_head_1203_ = lean_ctor_get(v_x_1202_, 0);
v_tail_1204_ = lean_ctor_get(v_x_1202_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_x_1202_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1206_ = v_x_1202_;
v_isShared_1207_ = v_isSharedCheck_1226_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_tail_1204_);
lean_inc(v_head_1203_);
lean_dec(v_x_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1226_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_before_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1224_; 
v_before_1208_ = lean_ctor_get(v_head_1203_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_head_1203_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_head_1203_, 1);
lean_dec(v_unused_1225_);
v___x_1210_ = v_head_1203_;
v_isShared_1211_ = v_isSharedCheck_1224_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_before_1208_);
lean_dec(v_head_1203_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1224_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 7);
lean_ctor_set(v___x_1210_, 1, v___x_1212_);
lean_ctor_set(v___x_1210_, 0, v_x_1201_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_x_1201_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 7);
lean_ctor_set(v___x_1206_, 1, v___x_1215_);
lean_ctor_set(v___x_1206_, 0, v___x_1214_);
v___x_1217_ = v___x_1206_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_MessageData_ofSyntax(v_before_1208_);
v___x_1219_ = l_Lean_indentD(v___x_1218_);
v___x_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1217_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v_x_1201_ = v___x_1220_;
v_x_1202_ = v_tail_1204_;
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
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1));
v___x_1231_ = l_Lean_MessageData_ofFormat(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(lean_object* v_msgData_1232_, lean_object* v_macroStack_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_toCold_1236_; lean_object* v_options_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_toCold_1236_ = lean_ctor_get(v___y_1234_, 0);
v_options_1237_ = lean_ctor_get(v_toCold_1236_, 2);
v___x_1238_ = l_Lean_Elab_pp_macroStack;
v___x_1239_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_options_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_macroStack_1233_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_msgData_1232_);
return v___x_1240_;
}
else
{
if (lean_obj_tag(v_macroStack_1233_) == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_msgData_1232_);
return v___x_1241_;
}
else
{
lean_object* v_head_1242_; lean_object* v_after_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1258_; 
v_head_1242_ = lean_ctor_get(v_macroStack_1233_, 0);
lean_inc(v_head_1242_);
v_after_1243_ = lean_ctor_get(v_head_1242_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_head_1242_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_head_1242_, 0);
lean_dec(v_unused_1259_);
v___x_1245_ = v_head_1242_;
v_isShared_1246_ = v_isSharedCheck_1258_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_after_1243_);
lean_dec(v_head_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1258_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 7);
lean_ctor_set(v___x_1245_, 1, v___x_1247_);
lean_ctor_set(v___x_1245_, 0, v_msgData_1232_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_msgData_1232_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_msgData_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1250_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_MessageData_ofSyntax(v_after_1243_);
v___x_1253_ = l_Lean_indentD(v___x_1252_);
v_msgData_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1254_, 0, v___x_1251_);
lean_ctor_set(v_msgData_1254_, 1, v___x_1253_);
v___x_1255_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(v_msgData_1254_, v_macroStack_1233_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___boxed(lean_object* v_msgData_1260_, lean_object* v_macroStack_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_1260_, v_macroStack_1261_, v___y_1262_);
lean_dec_ref(v___y_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_ref_1273_; lean_object* v___x_1274_; lean_object* v_a_1275_; lean_object* v_macroStack_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_ref_1273_ = lean_ctor_get(v___y_1270_, 2);
v___x_1274_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_1265_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v_macroStack_1276_ = lean_ctor_get(v___y_1266_, 1);
v___x_1277_ = l_Lean_Elab_getBetterRef(v_ref_1273_, v_macroStack_1276_);
lean_inc(v_macroStack_1276_);
v___x_1278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_a_1275_, v_macroStack_1276_, v___y_1270_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1277_);
lean_ctor_set(v___x_1283_, 1, v_a_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg___boxed(lean_object* v_msg_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(lean_object* v_ref_1297_, lean_object* v_msg_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_toCold_1306_; lean_object* v_currRecDepth_1307_; lean_object* v_ref_1308_; uint8_t v_diag_1309_; uint8_t v_suppressElabErrors_1310_; lean_object* v_ref_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_toCold_1306_ = lean_ctor_get(v___y_1303_, 0);
v_currRecDepth_1307_ = lean_ctor_get(v___y_1303_, 1);
v_ref_1308_ = lean_ctor_get(v___y_1303_, 2);
v_diag_1309_ = lean_ctor_get_uint8(v___y_1303_, sizeof(void*)*3);
v_suppressElabErrors_1310_ = lean_ctor_get_uint8(v___y_1303_, sizeof(void*)*3 + 1);
v_ref_1311_ = l_Lean_replaceRef(v_ref_1297_, v_ref_1308_);
lean_inc(v_currRecDepth_1307_);
lean_inc_ref(v_toCold_1306_);
v___x_1312_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1312_, 0, v_toCold_1306_);
lean_ctor_set(v___x_1312_, 1, v_currRecDepth_1307_);
lean_ctor_set(v___x_1312_, 2, v_ref_1311_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*3, v_diag_1309_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*3 + 1, v_suppressElabErrors_1310_);
v___x_1313_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___x_1312_, v___y_1304_);
lean_dec_ref_known(v___x_1312_, 3);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg___boxed(lean_object* v_ref_1314_, lean_object* v_msg_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1314_, v_msg_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v_ref_1314_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(lean_object* v_msg_1324_, lean_object* v_declHint_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v_env_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_st_ref_get(v___y_1326_);
v_env_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc_ref(v_env_1329_);
lean_dec(v___x_1328_);
v___x_1330_ = l_Lean_Name_isAnonymous(v_declHint_1325_);
if (v___x_1330_ == 0)
{
uint8_t v_isExporting_1331_; 
v_isExporting_1331_ = lean_ctor_get_uint8(v_env_1329_, sizeof(void*)*8);
if (v_isExporting_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec_ref(v_env_1329_);
lean_dec(v_declHint_1325_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_msg_1324_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
lean_inc_ref(v_env_1329_);
v___x_1333_ = l_Lean_Environment_setExporting(v_env_1329_, v___x_1330_);
lean_inc(v_declHint_1325_);
lean_inc_ref(v___x_1333_);
v___x_1334_ = l_Lean_Environment_contains(v___x_1333_, v_declHint_1325_, v_isExporting_1331_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref(v___x_1333_);
lean_dec_ref(v_env_1329_);
lean_dec(v_declHint_1325_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_msg_1324_);
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_c_1343_; lean_object* v___x_1344_; 
v___x_1336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1337_ = lean_unsigned_to_nat(32u);
v___x_1338_ = lean_mk_empty_array_with_capacity(v___x_1337_);
lean_dec_ref(v___x_1338_);
v___x_1339_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1340_ = l_Lean_Options_empty;
v___x_1341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1333_);
lean_ctor_set(v___x_1341_, 1, v___x_1336_);
lean_ctor_set(v___x_1341_, 2, v___x_1339_);
lean_ctor_set(v___x_1341_, 3, v___x_1340_);
lean_inc(v_declHint_1325_);
v___x_1342_ = l_Lean_MessageData_ofConstName(v_declHint_1325_, v___x_1330_);
v_c_1343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1343_, 0, v___x_1341_);
lean_ctor_set(v_c_1343_, 1, v___x_1342_);
v___x_1344_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1329_, v_declHint_1325_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v_env_1329_);
lean_dec(v_declHint_1325_);
v___x_1345_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_c_1343_);
v___x_1347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_MessageData_note(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_msg_1324_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1387_; 
v_val_1352_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1354_ = v___x_1344_;
v_isShared_1355_ = v_isSharedCheck_1387_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v___x_1344_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1387_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_mod_1359_; uint8_t v___x_1360_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = l_Lean_Environment_header(v_env_1329_);
lean_dec_ref(v_env_1329_);
v___x_1358_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1357_);
v_mod_1359_ = lean_array_get(v___x_1356_, v___x_1358_, v_val_1352_);
lean_dec(v_val_1352_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = l_Lean_isPrivateName(v_declHint_1325_);
lean_dec(v_declHint_1325_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1361_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_c_1343_);
v___x_1363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_MessageData_ofName(v_mod_1359_);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_MessageData_note(v___x_1368_);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_msg_1324_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1370_);
v___x_1372_ = v___x_1354_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1374_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v_c_1343_);
v___x_1376_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_MessageData_ofName(v_mod_1359_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_MessageData_note(v___x_1381_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_msg_1324_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1383_);
v___x_1385_ = v___x_1354_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1388_; 
lean_dec_ref(v_env_1329_);
lean_dec(v_declHint_1325_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_msg_1324_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg___boxed(lean_object* v_msg_1389_, lean_object* v_declHint_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1389_, v_declHint_1390_, v___y_1391_);
lean_dec(v___y_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(lean_object* v_msg_1394_, lean_object* v_declHint_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v___x_1403_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1394_, v_declHint_1395_, v___y_1401_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = l_Lean_unknownIdentifierMessageTag;
v___x_1409_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_a_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1409_);
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23___boxed(lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1414_, v_declHint_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(lean_object* v_ref_1424_, lean_object* v_msg_1425_, lean_object* v_declHint_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_a_1435_; lean_object* v___x_1436_; 
v___x_1434_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1425_, v_declHint_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1424_, v_a_1435_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg___boxed(lean_object* v_ref_1437_, lean_object* v_msg_1438_, lean_object* v_declHint_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1437_, v_msg_1438_, v_declHint_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v_ref_1437_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(lean_object* v_ref_1448_, lean_object* v_constName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1457_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1458_ = 0;
lean_inc(v_constName_1449_);
v___x_1459_ = l_Lean_MessageData_ofConstName(v_constName_1449_, v___x_1458_);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1448_, v___x_1462_, v_constName_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_ref_1464_, lean_object* v_constName_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1464_, v_constName_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v_ref_1464_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(lean_object* v_constName_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_ref_1482_; lean_object* v___x_1483_; 
v_ref_1482_ = lean_ctor_get(v___y_1479_, 2);
v___x_1483_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1482_, v_constName_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg___boxed(lean_object* v_constName_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(lean_object* v_constName_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v_env_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_st_ref_get(v___y_1499_);
v_env_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_env_1502_);
lean_dec(v___x_1501_);
v___x_1503_ = 0;
lean_inc(v_constName_1493_);
v___x_1504_ = l_Lean_Environment_find_x3f(v_env_1502_, v_constName_1493_, v___x_1503_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1505_;
}
else
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_constName_1493_);
v_val_1506_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1504_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v___x_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_val_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2___boxed(lean_object* v_constName_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_constName_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1522_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(uint8_t v_suppressElabErrors_1529_, uint8_t v___y_1530_, lean_object* v_x_1531_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 1)
{
lean_object* v_pre_1532_; 
v_pre_1532_ = lean_ctor_get(v_x_1531_, 0);
switch(lean_obj_tag(v_pre_1532_))
{
case 1:
{
lean_object* v_pre_1533_; 
v_pre_1533_ = lean_ctor_get(v_pre_1532_, 0);
switch(lean_obj_tag(v_pre_1533_))
{
case 0:
{
lean_object* v_str_1534_; lean_object* v_str_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_str_1534_ = lean_ctor_get(v_x_1531_, 1);
v_str_1535_ = lean_ctor_get(v_pre_1532_, 1);
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8));
v___x_1537_ = lean_string_dec_eq(v_str_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2));
v___x_1539_ = lean_string_dec_eq(v_str_1535_, v___x_1538_);
if (v___x_1539_ == 0)
{
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___x_1541_ = lean_string_dec_eq(v_str_1534_, v___x_1540_);
if (v___x_1541_ == 0)
{
return v___x_1541_;
}
else
{
return v_suppressElabErrors_1529_;
}
}
}
else
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1));
v___x_1543_ = lean_string_dec_eq(v_str_1534_, v___x_1542_);
if (v___x_1543_ == 0)
{
return v___x_1543_;
}
else
{
return v_suppressElabErrors_1529_;
}
}
}
case 1:
{
lean_object* v_pre_1544_; 
v_pre_1544_ = lean_ctor_get(v_pre_1533_, 0);
if (lean_obj_tag(v_pre_1544_) == 0)
{
lean_object* v_str_1545_; lean_object* v_str_1546_; lean_object* v_str_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_str_1545_ = lean_ctor_get(v_x_1531_, 1);
v_str_1546_ = lean_ctor_get(v_pre_1532_, 1);
v_str_1547_ = lean_ctor_get(v_pre_1533_, 1);
v___x_1548_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2));
v___x_1549_ = lean_string_dec_eq(v_str_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3));
v___x_1551_ = lean_string_dec_eq(v_str_1546_, v___x_1550_);
if (v___x_1551_ == 0)
{
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4));
v___x_1553_ = lean_string_dec_eq(v_str_1545_, v___x_1552_);
if (v___x_1553_ == 0)
{
return v___x_1553_;
}
else
{
return v_suppressElabErrors_1529_;
}
}
}
}
else
{
return v___y_1530_;
}
}
default: 
{
return v___y_1530_;
}
}
}
case 0:
{
lean_object* v_str_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_str_1554_ = lean_ctor_get(v_x_1531_, 1);
v___x_1555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5));
v___x_1556_ = lean_string_dec_eq(v_str_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1529_;
}
}
default: 
{
return v___y_1530_;
}
}
}
else
{
return v___y_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1557_, lean_object* v___y_1558_, lean_object* v_x_1559_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1560_; uint8_t v___y_49104__boxed_1561_; uint8_t v_res_1562_; lean_object* v_r_1563_; 
v_suppressElabErrors_boxed_1560_ = lean_unbox(v_suppressElabErrors_1557_);
v___y_49104__boxed_1561_ = lean_unbox(v___y_1558_);
v_res_1562_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(v_suppressElabErrors_boxed_1560_, v___y_49104__boxed_1561_, v_x_1559_);
lean_dec(v_x_1559_);
v_r_1563_ = lean_box(v_res_1562_);
return v_r_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1564_, lean_object* v_msgData_1565_, uint8_t v_severity_1566_, uint8_t v_isSilent_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; uint8_t v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; uint8_t v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1636_; lean_object* v___y_1637_; uint8_t v___y_1638_; lean_object* v___y_1639_; uint8_t v___y_1640_; lean_object* v___y_1641_; uint8_t v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1647_; lean_object* v___y_1648_; uint8_t v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; uint8_t v___y_1653_; uint8_t v___x_1658_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; uint8_t v___y_1666_; uint8_t v___y_1668_; uint8_t v___x_1684_; 
v___x_1658_ = 2;
v___x_1684_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1566_, v___x_1658_);
if (v___x_1684_ == 0)
{
v___y_1668_ = v___x_1684_;
goto v___jp_1667_;
}
else
{
uint8_t v___x_1685_; 
lean_inc_ref(v_msgData_1565_);
v___x_1685_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1565_);
v___y_1668_ = v___x_1685_;
goto v___jp_1667_;
}
v___jp_1573_:
{
lean_object* v___x_1583_; lean_object* v_toCold_1584_; lean_object* v_currNamespace_1585_; lean_object* v_openDecls_1586_; lean_object* v_env_1587_; lean_object* v_nextMacroScope_1588_; lean_object* v_ngen_1589_; lean_object* v_auxDeclNGen_1590_; lean_object* v_traceState_1591_; lean_object* v_cache_1592_; lean_object* v_messages_1593_; lean_object* v_infoState_1594_; lean_object* v_snapshotTasks_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1609_; 
v___x_1583_ = lean_st_ref_take(v___y_1582_);
v_toCold_1584_ = lean_ctor_get(v___y_1581_, 0);
v_currNamespace_1585_ = lean_ctor_get(v_toCold_1584_, 4);
v_openDecls_1586_ = lean_ctor_get(v_toCold_1584_, 5);
v_env_1587_ = lean_ctor_get(v___x_1583_, 0);
v_nextMacroScope_1588_ = lean_ctor_get(v___x_1583_, 1);
v_ngen_1589_ = lean_ctor_get(v___x_1583_, 2);
v_auxDeclNGen_1590_ = lean_ctor_get(v___x_1583_, 3);
v_traceState_1591_ = lean_ctor_get(v___x_1583_, 4);
v_cache_1592_ = lean_ctor_get(v___x_1583_, 5);
v_messages_1593_ = lean_ctor_get(v___x_1583_, 6);
v_infoState_1594_ = lean_ctor_get(v___x_1583_, 7);
v_snapshotTasks_1595_ = lean_ctor_get(v___x_1583_, 8);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1597_ = v___x_1583_;
v_isShared_1598_ = v_isSharedCheck_1609_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_snapshotTasks_1595_);
lean_inc(v_infoState_1594_);
lean_inc(v_messages_1593_);
lean_inc(v_cache_1592_);
lean_inc(v_traceState_1591_);
lean_inc(v_auxDeclNGen_1590_);
lean_inc(v_ngen_1589_);
lean_inc(v_nextMacroScope_1588_);
lean_inc(v_env_1587_);
lean_dec(v___x_1583_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1609_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
lean_inc(v_openDecls_1586_);
lean_inc(v_currNamespace_1585_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_currNamespace_1585_);
lean_ctor_set(v___x_1599_, 1, v_openDecls_1586_);
v___x_1600_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___y_1574_);
lean_inc_ref(v___y_1576_);
lean_inc_ref(v___y_1579_);
v___x_1601_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1601_, 0, v___y_1579_);
lean_ctor_set(v___x_1601_, 1, v___y_1575_);
lean_ctor_set(v___x_1601_, 2, v___y_1577_);
lean_ctor_set(v___x_1601_, 3, v___y_1576_);
lean_ctor_set(v___x_1601_, 4, v___x_1600_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*5, v___y_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*5 + 1, v___y_1578_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*5 + 2, v_isSilent_1567_);
v___x_1602_ = l_Lean_MessageLog_add(v___x_1601_, v_messages_1593_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 6, v___x_1602_);
v___x_1604_ = v___x_1597_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_env_1587_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_nextMacroScope_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_ngen_1589_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_auxDeclNGen_1590_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_traceState_1591_);
lean_ctor_set(v_reuseFailAlloc_1608_, 5, v_cache_1592_);
lean_ctor_set(v_reuseFailAlloc_1608_, 6, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 7, v_infoState_1594_);
lean_ctor_set(v_reuseFailAlloc_1608_, 8, v_snapshotTasks_1595_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_st_ref_put(v___y_1582_, v___x_1604_);
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
}
}
v___jp_1610_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1634_; 
v___x_1619_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1565_);
v___x_1620_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v___x_1619_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1634_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1634_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_inc_ref_n(v___y_1612_, 2);
v___x_1625_ = l_Lean_FileMap_toPosition(v___y_1612_, v___y_1615_);
lean_dec(v___y_1615_);
v___x_1626_ = l_Lean_FileMap_toPosition(v___y_1612_, v___y_1618_);
lean_dec(v___y_1618_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v___x_1628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
if (v___y_1613_ == 0)
{
lean_del_object(v___x_1623_);
lean_dec_ref(v___y_1611_);
v___y_1574_ = v_a_1621_;
v___y_1575_ = v___x_1625_;
v___y_1576_ = v___x_1628_;
v___y_1577_ = v___x_1627_;
v___y_1578_ = v___y_1614_;
v___y_1579_ = v___y_1616_;
v___y_1580_ = v___y_1617_;
v___y_1581_ = v___y_1570_;
v___y_1582_ = v___y_1571_;
goto v___jp_1573_;
}
else
{
uint8_t v___x_1629_; 
lean_inc(v_a_1621_);
v___x_1629_ = l_Lean_MessageData_hasTag(v___y_1611_, v_a_1621_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1627_, 1);
lean_dec_ref(v___x_1625_);
lean_dec(v_a_1621_);
v___x_1630_ = lean_box(0);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1630_);
v___x_1632_ = v___x_1623_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
else
{
lean_del_object(v___x_1623_);
v___y_1574_ = v_a_1621_;
v___y_1575_ = v___x_1625_;
v___y_1576_ = v___x_1628_;
v___y_1577_ = v___x_1627_;
v___y_1578_ = v___y_1614_;
v___y_1579_ = v___y_1616_;
v___y_1580_ = v___y_1617_;
v___y_1581_ = v___y_1570_;
v___y_1582_ = v___y_1571_;
goto v___jp_1573_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Syntax_getTailPos_x3f(v___y_1639_, v___y_1642_);
lean_dec(v___y_1639_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_inc(v___y_1643_);
v___y_1611_ = v___y_1636_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___y_1638_;
v___y_1614_ = v___y_1640_;
v___y_1615_ = v___y_1643_;
v___y_1616_ = v___y_1641_;
v___y_1617_ = v___y_1642_;
v___y_1618_ = v___y_1643_;
goto v___jp_1610_;
}
else
{
lean_object* v_val_1645_; 
v_val_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___y_1611_ = v___y_1636_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___y_1638_;
v___y_1614_ = v___y_1640_;
v___y_1615_ = v___y_1643_;
v___y_1616_ = v___y_1641_;
v___y_1617_ = v___y_1642_;
v___y_1618_ = v_val_1645_;
goto v___jp_1610_;
}
}
v___jp_1646_:
{
lean_object* v_ref_1654_; lean_object* v___x_1655_; 
v_ref_1654_ = l_Lean_replaceRef(v_ref_1564_, v___y_1650_);
v___x_1655_ = l_Lean_Syntax_getPos_x3f(v_ref_1654_, v___y_1652_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_unsigned_to_nat(0u);
v___y_1636_ = v___y_1647_;
v___y_1637_ = v___y_1648_;
v___y_1638_ = v___y_1649_;
v___y_1639_ = v_ref_1654_;
v___y_1640_ = v___y_1653_;
v___y_1641_ = v___y_1651_;
v___y_1642_ = v___y_1652_;
v___y_1643_ = v___x_1656_;
goto v___jp_1635_;
}
else
{
lean_object* v_val_1657_; 
v_val_1657_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1655_, 1);
v___y_1636_ = v___y_1647_;
v___y_1637_ = v___y_1648_;
v___y_1638_ = v___y_1649_;
v___y_1639_ = v_ref_1654_;
v___y_1640_ = v___y_1653_;
v___y_1641_ = v___y_1651_;
v___y_1642_ = v___y_1652_;
v___y_1643_ = v_val_1657_;
goto v___jp_1635_;
}
}
v___jp_1659_:
{
if (v___y_1666_ == 0)
{
v___y_1647_ = v___y_1662_;
v___y_1648_ = v___y_1660_;
v___y_1649_ = v___y_1663_;
v___y_1650_ = v___y_1664_;
v___y_1651_ = v___y_1661_;
v___y_1652_ = v___y_1665_;
v___y_1653_ = v_severity_1566_;
goto v___jp_1646_;
}
else
{
v___y_1647_ = v___y_1662_;
v___y_1648_ = v___y_1660_;
v___y_1649_ = v___y_1663_;
v___y_1650_ = v___y_1664_;
v___y_1651_ = v___y_1661_;
v___y_1652_ = v___y_1665_;
v___y_1653_ = v___x_1658_;
goto v___jp_1646_;
}
}
v___jp_1667_:
{
if (v___y_1668_ == 0)
{
lean_object* v_toCold_1669_; lean_object* v_ref_1670_; uint8_t v_suppressElabErrors_1671_; lean_object* v_fileName_1672_; lean_object* v_fileMap_1673_; lean_object* v_options_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___f_1677_; uint8_t v___x_1678_; uint8_t v___x_1679_; 
v_toCold_1669_ = lean_ctor_get(v___y_1570_, 0);
v_ref_1670_ = lean_ctor_get(v___y_1570_, 2);
v_suppressElabErrors_1671_ = lean_ctor_get_uint8(v___y_1570_, sizeof(void*)*3 + 1);
v_fileName_1672_ = lean_ctor_get(v_toCold_1669_, 0);
v_fileMap_1673_ = lean_ctor_get(v_toCold_1669_, 1);
v_options_1674_ = lean_ctor_get(v_toCold_1669_, 2);
v___x_1675_ = lean_box(v_suppressElabErrors_1671_);
v___x_1676_ = lean_box(v___y_1668_);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1677_, 0, v___x_1675_);
lean_closure_set(v___f_1677_, 1, v___x_1676_);
v___x_1678_ = 1;
v___x_1679_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1566_, v___x_1678_);
if (v___x_1679_ == 0)
{
v___y_1660_ = v_fileMap_1673_;
v___y_1661_ = v_fileName_1672_;
v___y_1662_ = v___f_1677_;
v___y_1663_ = v_suppressElabErrors_1671_;
v___y_1664_ = v_ref_1670_;
v___y_1665_ = v___y_1668_;
v___y_1666_ = v___x_1679_;
goto v___jp_1659_;
}
else
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = l_Lean_warningAsError;
v___x_1681_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_options_1674_, v___x_1680_);
v___y_1660_ = v_fileMap_1673_;
v___y_1661_ = v_fileName_1672_;
v___y_1662_ = v___f_1677_;
v___y_1663_ = v_suppressElabErrors_1671_;
v___y_1664_ = v_ref_1670_;
v___y_1665_ = v___y_1668_;
v___y_1666_ = v___x_1681_;
goto v___jp_1659_;
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref(v_msgData_1565_);
v___x_1682_ = lean_box(0);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1686_, lean_object* v_msgData_1687_, lean_object* v_severity_1688_, lean_object* v_isSilent_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v_severity_boxed_1695_; uint8_t v_isSilent_boxed_1696_; lean_object* v_res_1697_; 
v_severity_boxed_1695_ = lean_unbox(v_severity_1688_);
v_isSilent_boxed_1696_ = lean_unbox(v_isSilent_1689_);
v_res_1697_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1686_, v_msgData_1687_, v_severity_boxed_1695_, v_isSilent_boxed_1696_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v_ref_1686_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(lean_object* v_msgData_1698_, uint8_t v_severity_1699_, uint8_t v_isSilent_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_ref_1708_; lean_object* v___x_1709_; 
v_ref_1708_ = lean_ctor_get(v___y_1705_, 2);
v___x_1709_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1708_, v_msgData_1698_, v_severity_1699_, v_isSilent_1700_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1710_, lean_object* v_severity_1711_, lean_object* v_isSilent_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v_severity_boxed_1720_; uint8_t v_isSilent_boxed_1721_; lean_object* v_res_1722_; 
v_severity_boxed_1720_ = lean_unbox(v_severity_1711_);
v_isSilent_boxed_1721_ = lean_unbox(v_isSilent_1712_);
v_res_1722_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1710_, v_severity_boxed_1720_, v_isSilent_boxed_1721_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(lean_object* v_msgData_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = 2;
v___x_1732_ = 0;
v___x_1733_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1723_, v___x_1731_, v___x_1732_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1___boxed(lean_object* v_msgData_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v_msgData_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(lean_object* v_ref_1743_, lean_object* v_msgData_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = 2;
v___x_1753_ = 0;
v___x_1754_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1743_, v_msgData_1744_, v___x_1752_, v___x_1753_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0___boxed(lean_object* v_ref_1755_, lean_object* v_msgData_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1755_, v_msgData_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v_ref_1755_);
return v_res_1764_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(lean_object* v_ex_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
if (lean_obj_tag(v_ex_1768_) == 0)
{
lean_object* v_ref_1776_; lean_object* v_msg_1777_; lean_object* v___x_1778_; 
v_ref_1776_ = lean_ctor_get(v_ex_1768_, 0);
lean_inc(v_ref_1776_);
v_msg_1777_ = lean_ctor_get(v_ex_1768_, 1);
lean_inc_ref(v_msg_1777_);
lean_dec_ref_known(v_ex_1768_, 2);
v___x_1778_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1776_, v_msg_1777_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v_ref_1776_);
return v___x_1778_;
}
else
{
lean_object* v_id_1779_; uint8_t v___y_1781_; uint8_t v___x_1803_; 
v_id_1779_ = lean_ctor_get(v_ex_1768_, 0);
lean_inc(v_id_1779_);
v___x_1803_ = l_Lean_Elab_isAbortExceptionId(v_id_1779_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Lean_Exception_isInterrupt(v_ex_1768_);
lean_dec_ref_known(v_ex_1768_, 2);
v___y_1781_ = v___x_1804_;
goto v___jp_1780_;
}
else
{
lean_dec_ref_known(v_ex_1768_, 2);
v___y_1781_ = v___x_1803_;
goto v___jp_1780_;
}
v___jp_1780_:
{
if (v___y_1781_ == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_InternalExceptionId_getName(v_id_1779_);
lean_dec(v_id_1779_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1);
v___x_1785_ = l_Lean_MessageData_ofName(v_a_1783_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v___x_1786_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1787_;
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1800_; 
v_a_1788_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1790_ = v___x_1782_;
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1782_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_ref_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v_ref_1792_ = lean_ctor_get(v___y_1773_, 2);
v___x_1793_ = lean_io_error_to_string(v_a_1788_);
v___x_1794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = l_Lean_MessageData_ofFormat(v___x_1794_);
lean_inc(v_ref_1792_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_ref_1792_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1796_);
v___x_1798_ = v___x_1790_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v_id_1779_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___boxed(lean_object* v_ex_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v_ex_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(lean_object* v_t_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v_infoState_1818_; uint8_t v_enabled_1819_; 
v___x_1817_ = lean_st_ref_get(v___y_1815_);
v_infoState_1818_ = lean_ctor_get(v___x_1817_, 7);
lean_inc_ref(v_infoState_1818_);
lean_dec(v___x_1817_);
v_enabled_1819_ = lean_ctor_get_uint8(v_infoState_1818_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1818_);
if (v_enabled_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_t_1814_);
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; lean_object* v_infoState_1823_; lean_object* v_env_1824_; lean_object* v_nextMacroScope_1825_; lean_object* v_ngen_1826_; lean_object* v_auxDeclNGen_1827_; lean_object* v_traceState_1828_; lean_object* v_cache_1829_; lean_object* v_messages_1830_; lean_object* v_snapshotTasks_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1853_; 
v___x_1822_ = lean_st_ref_take(v___y_1815_);
v_infoState_1823_ = lean_ctor_get(v___x_1822_, 7);
v_env_1824_ = lean_ctor_get(v___x_1822_, 0);
v_nextMacroScope_1825_ = lean_ctor_get(v___x_1822_, 1);
v_ngen_1826_ = lean_ctor_get(v___x_1822_, 2);
v_auxDeclNGen_1827_ = lean_ctor_get(v___x_1822_, 3);
v_traceState_1828_ = lean_ctor_get(v___x_1822_, 4);
v_cache_1829_ = lean_ctor_get(v___x_1822_, 5);
v_messages_1830_ = lean_ctor_get(v___x_1822_, 6);
v_snapshotTasks_1831_ = lean_ctor_get(v___x_1822_, 8);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1833_ = v___x_1822_;
v_isShared_1834_ = v_isSharedCheck_1853_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_snapshotTasks_1831_);
lean_inc(v_infoState_1823_);
lean_inc(v_messages_1830_);
lean_inc(v_cache_1829_);
lean_inc(v_traceState_1828_);
lean_inc(v_auxDeclNGen_1827_);
lean_inc(v_ngen_1826_);
lean_inc(v_nextMacroScope_1825_);
lean_inc(v_env_1824_);
lean_dec(v___x_1822_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1853_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v_enabled_1835_; lean_object* v_assignment_1836_; lean_object* v_lazyAssignment_1837_; lean_object* v_trees_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1852_; 
v_enabled_1835_ = lean_ctor_get_uint8(v_infoState_1823_, sizeof(void*)*3);
v_assignment_1836_ = lean_ctor_get(v_infoState_1823_, 0);
v_lazyAssignment_1837_ = lean_ctor_get(v_infoState_1823_, 1);
v_trees_1838_ = lean_ctor_get(v_infoState_1823_, 2);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_infoState_1823_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1840_ = v_infoState_1823_;
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_trees_1838_);
lean_inc(v_lazyAssignment_1837_);
lean_inc(v_assignment_1836_);
lean_dec(v_infoState_1823_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_PersistentArray_push___redArg(v_trees_1838_, v_t_1814_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 2, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_assignment_1836_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_lazyAssignment_1837_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v___x_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*3, v_enabled_1835_);
v___x_1844_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 7, v___x_1844_);
v___x_1846_ = v___x_1833_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_env_1824_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_nextMacroScope_1825_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_ngen_1826_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_auxDeclNGen_1827_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_traceState_1828_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_cache_1829_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v_messages_1830_);
lean_ctor_set(v_reuseFailAlloc_1850_, 7, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1850_, 8, v_snapshotTasks_1831_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_st_ref_put(v___y_1815_, v___x_1846_);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_t_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_1854_, v___y_1855_);
lean_dec(v___y_1855_);
return v_res_1857_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = lean_unsigned_to_nat(32u);
v___x_1859_ = lean_mk_empty_array_with_capacity(v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1861_ = ((size_t)5ULL);
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_unsigned_to_nat(32u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1865_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0);
v___x_1866_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___x_1864_);
lean_ctor_set(v___x_1866_, 2, v___x_1862_);
lean_ctor_set(v___x_1866_, 3, v___x_1862_);
lean_ctor_set_usize(v___x_1866_, 4, v___x_1861_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(lean_object* v_t_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v_infoState_1876_; uint8_t v_enabled_1877_; 
v___x_1875_ = lean_st_ref_get(v___y_1873_);
v_infoState_1876_ = lean_ctor_get(v___x_1875_, 7);
lean_inc_ref(v_infoState_1876_);
lean_dec(v___x_1875_);
v_enabled_1877_ = lean_ctor_get_uint8(v_infoState_1876_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1876_);
if (v_enabled_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec_ref(v_t_1867_);
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_t_1867_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v___x_1881_, v___y_1873_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___boxed(lean_object* v_t_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v_t_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(lean_object* v_info_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1900_, 0, v_info_1892_);
v___x_1901_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v___x_1900_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1___boxed(lean_object* v_info_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v_info_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1910_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13));
v___x_1950_ = l_String_toRawSubstring_x27(v___x_1949_);
return v___x_1950_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9));
v___x_1974_ = l_String_toRawSubstring_x27(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(uint8_t v___x_1989_, lean_object* v_option_1990_, lean_object* v_fst_1991_, uint8_t v___x_1992_, lean_object* v_fst_1993_, lean_object* v_fst_1994_, lean_object* v_snd_1995_, lean_object* v_mkStructInst_1996_, lean_object* v_seenFields_1997_, lean_object* v_fields_1998_, lean_object* v_value_1999_, lean_object* v_____r_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___y_2009_; lean_object* v_source_x3f_2010_; lean_object* v_seenFields_2011_; lean_object* v_fields_2012_; lean_object* v___y_2013_; lean_object* v_value_2037_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8));
lean_inc(v_value_1999_);
v___x_2051_ = l_Lean_Syntax_isOfKind(v_value_1999_, v___x_2050_);
if (v___x_2051_ == 0)
{
v_value_2037_ = v_value_1999_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = l_Lean_Syntax_getArg(v_value_1999_, v___x_2052_);
if (v___x_1989_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10));
lean_inc(v___x_2053_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v___x_2053_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v___x_2053_);
v_value_2037_ = v_value_1999_;
goto v___jp_2036_;
}
else
{
goto v___jp_2054_;
}
}
else
{
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v_toCold_2055_; lean_object* v_ref_2056_; lean_object* v_quotContext_2057_; lean_object* v_currMacroScope_2058_; lean_object* v_ref_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_toCold_2055_ = lean_ctor_get(v___y_2005_, 0);
v_ref_2056_ = lean_ctor_get(v___y_2005_, 2);
v_quotContext_2057_ = lean_ctor_get(v_toCold_2055_, 8);
v_currMacroScope_2058_ = lean_ctor_get(v_toCold_2055_, 9);
v_ref_2059_ = l_Lean_replaceRef(v_value_1999_, v_ref_2056_);
lean_dec(v_value_1999_);
v___x_2060_ = l_Lean_SourceInfo_fromRef(v_ref_2059_, v___x_1989_);
lean_dec(v_ref_2059_);
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_2062_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14);
v___x_2063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17));
lean_inc_n(v_currMacroScope_2058_, 2);
lean_inc_n(v_quotContext_2057_, 2);
v___x_2064_ = l_Lean_addMacroScope(v_quotContext_2057_, v___x_2063_, v_currMacroScope_2058_);
v___x_2065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20));
lean_inc_n(v___x_2060_, 7);
v___x_2066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2060_);
lean_ctor_set(v___x_2066_, 1, v___x_2062_);
lean_ctor_set(v___x_2066_, 2, v___x_2064_);
lean_ctor_set(v___x_2066_, 3, v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22));
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23));
v___x_2070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2060_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25));
v___x_2073_ = l_Lean_addMacroScope(v_quotContext_2057_, v___x_2072_, v_currMacroScope_2058_);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29));
v___x_2075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2060_);
lean_ctor_set(v___x_2075_, 1, v___x_2071_);
lean_ctor_set(v___x_2075_, 2, v___x_2073_);
lean_ctor_set(v___x_2075_, 3, v___x_2074_);
v___x_2076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30));
v___x_2077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2060_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_2079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2060_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = l_Lean_Syntax_node5(v___x_2060_, v___x_2068_, v___x_2070_, v___x_2075_, v___x_2077_, v___x_2053_, v___x_2079_);
v___x_2081_ = l_Lean_Syntax_node1(v___x_2060_, v___x_2067_, v___x_2080_);
v___x_2082_ = l_Lean_Syntax_node2(v___x_2060_, v___x_2061_, v___x_2066_, v___x_2081_);
v_value_2037_ = v___x_2082_;
goto v___jp_2036_;
}
}
v___jp_2008_:
{
lean_object* v_ref_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_ref_2014_ = lean_ctor_get(v___y_2013_, 2);
v___x_2015_ = l_Lean_SourceInfo_fromRef(v_ref_2014_, v___x_1989_);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1));
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3));
lean_inc(v_fst_1991_);
v___x_2018_ = l_Lean_mkCIdentFrom(v_option_1990_, v_fst_1991_, v___x_1992_);
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2015_, 5);
v___x_2021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2015_);
lean_ctor_set(v___x_2021_, 1, v___x_2019_);
lean_ctor_set(v___x_2021_, 2, v___x_2020_);
lean_inc_ref_n(v___x_2021_, 3);
v___x_2022_ = l_Lean_Syntax_node2(v___x_2015_, v___x_2017_, v___x_2018_, v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5));
v___x_2024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_2025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2015_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_Syntax_node3(v___x_2015_, v___x_2023_, v___x_2025_, v___x_2021_, v___y_2009_);
v___x_2027_ = l_Lean_Syntax_node3(v___x_2015_, v___x_2019_, v___x_2021_, v___x_2021_, v___x_2026_);
v___x_2028_ = l_Lean_Syntax_node2(v___x_2015_, v___x_2016_, v___x_2022_, v___x_2027_);
v___x_2029_ = lean_array_push(v_fields_2012_, v___x_2028_);
v___x_2030_ = l_Lean_NameSet_insert(v_seenFields_2011_, v_fst_1991_);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2029_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_source_x3f_2010_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2031_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
v___jp_2036_:
{
uint8_t v___x_2038_; 
v___x_2038_ = l_Lean_NameSet_contains(v_fst_1993_, v_fst_1991_);
if (v___x_2038_ == 0)
{
lean_dec_ref(v_fields_1998_);
lean_dec(v_seenFields_1997_);
lean_dec_ref(v_mkStructInst_1996_);
v___y_2009_ = v_value_2037_;
v_source_x3f_2010_ = v_fst_1994_;
v_seenFields_2011_ = v_fst_1993_;
v_fields_2012_ = v_snd_1995_;
v___y_2013_ = v___y_2005_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2039_; 
lean_dec(v_fst_1993_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
v___x_2039_ = lean_apply_9(v_mkStructInst_1996_, v_fst_1994_, v_snd_1995_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, lean_box(0));
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_a_2040_);
v___y_2009_ = v_value_2037_;
v_source_x3f_2010_ = v___x_2041_;
v_seenFields_2011_ = v_seenFields_1997_;
v_fields_2012_ = v_fields_1998_;
v___y_2013_ = v___y_2005_;
goto v___jp_2008_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_value_2037_);
lean_dec_ref(v_fields_1998_);
lean_dec(v_seenFields_1997_);
lean_dec(v_fst_1991_);
v_a_2042_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2039_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2039_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v___x_2085_ = _args[0];
lean_object* v_option_2086_ = _args[1];
lean_object* v_fst_2087_ = _args[2];
lean_object* v___x_2088_ = _args[3];
lean_object* v_fst_2089_ = _args[4];
lean_object* v_fst_2090_ = _args[5];
lean_object* v_snd_2091_ = _args[6];
lean_object* v_mkStructInst_2092_ = _args[7];
lean_object* v_seenFields_2093_ = _args[8];
lean_object* v_fields_2094_ = _args[9];
lean_object* v_value_2095_ = _args[10];
lean_object* v_____r_2096_ = _args[11];
lean_object* v___y_2097_ = _args[12];
lean_object* v___y_2098_ = _args[13];
lean_object* v___y_2099_ = _args[14];
lean_object* v___y_2100_ = _args[15];
lean_object* v___y_2101_ = _args[16];
lean_object* v___y_2102_ = _args[17];
lean_object* v___y_2103_ = _args[18];
_start:
{
uint8_t v___x_49856__boxed_2104_; uint8_t v___x_49858__boxed_2105_; lean_object* v_res_2106_; 
v___x_49856__boxed_2104_ = lean_unbox(v___x_2085_);
v___x_49858__boxed_2105_ = lean_unbox(v___x_2088_);
v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_49856__boxed_2104_, v_option_2086_, v_fst_2087_, v___x_49858__boxed_2105_, v_fst_2089_, v_fst_2090_, v_snd_2091_, v_mkStructInst_2092_, v_seenFields_2093_, v_fields_2094_, v_value_2095_, v_____r_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v_option_2086_);
return v_res_2106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = lean_box(1);
v___x_2113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
v___x_2115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2113_);
lean_ctor_set(v___x_2115_, 2, v___x_2112_);
return v___x_2115_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_box(0);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4));
v___x_2120_ = l_Lean_Expr_const___override(v___x_2119_, v___x_2118_);
return v___x_2120_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8));
v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(lean_object* v_structName_2127_, uint8_t v_recover_2128_, lean_object* v_as_2129_, size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_fst_2141_; lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_usize_dec_lt(v_i_2131_, v_sz_2130_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec(v_structName_2127_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_b_2132_);
return v___x_2151_;
}
else
{
lean_object* v_snd_2152_; lean_object* v_fst_2153_; lean_object* v_fst_2154_; lean_object* v_snd_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2260_; 
v_snd_2152_ = lean_ctor_get(v_b_2132_, 1);
lean_inc(v_snd_2152_);
v_fst_2153_ = lean_ctor_get(v_b_2132_, 0);
lean_inc(v_fst_2153_);
lean_dec_ref(v_b_2132_);
v_fst_2154_ = lean_ctor_get(v_snd_2152_, 0);
v_snd_2155_ = lean_ctor_get(v_snd_2152_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_snd_2152_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2157_ = v_snd_2152_;
v_isShared_2158_ = v_isSharedCheck_2260_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_snd_2155_);
lean_inc(v_fst_2154_);
lean_dec(v_snd_2152_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2260_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___y_2160_; uint8_t v___y_2161_; lean_object* v_a_2174_; lean_object* v___y_2178_; lean_object* v_a_2186_; lean_object* v_ref_2187_; lean_object* v_option_2188_; lean_object* v_value_2189_; uint8_t v_bool_2190_; lean_object* v_mkStructInst_2191_; lean_object* v_seenFields_2192_; lean_object* v_fields_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_a_2186_ = lean_array_uget_borrowed(v_as_2129_, v_i_2131_);
v_ref_2187_ = lean_ctor_get(v_a_2186_, 0);
v_option_2188_ = lean_ctor_get(v_a_2186_, 1);
v_value_2189_ = lean_ctor_get(v_a_2186_, 2);
v_bool_2190_ = lean_ctor_get_uint8(v_a_2186_, sizeof(void*)*3);
lean_inc(v_structName_2127_);
v_mkStructInst_2191_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed), 10, 1);
lean_closure_set(v_mkStructInst_2191_, 0, v_structName_2127_);
v_seenFields_2192_ = l_Lean_NameSet_empty;
v_fields_2193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v___x_2194_ = l_Lean_TSyntax_getId(v_option_2188_);
v___x_2195_ = l_Lean_Name_eraseMacroScopes(v___x_2194_);
lean_dec(v___x_2194_);
v___x_2196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7));
v___x_2197_ = lean_name_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3);
lean_inc(v___x_2195_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2195_);
lean_inc(v_structName_2127_);
lean_inc(v_option_2188_);
v___x_2200_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2200_, 0, v_option_2188_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
lean_ctor_set(v___x_2200_, 2, v___x_2198_);
lean_ctor_set(v___x_2200_, 3, v_structName_2127_);
v___x_2201_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v___x_2200_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_toCold_2202_; lean_object* v_currRecDepth_2203_; lean_object* v_ref_2204_; uint8_t v_diag_2205_; uint8_t v_suppressElabErrors_2206_; lean_object* v_ref_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref_known(v___x_2201_, 1);
v_toCold_2202_ = lean_ctor_get(v___y_2137_, 0);
v_currRecDepth_2203_ = lean_ctor_get(v___y_2137_, 1);
v_ref_2204_ = lean_ctor_get(v___y_2137_, 2);
v_diag_2205_ = lean_ctor_get_uint8(v___y_2137_, sizeof(void*)*3);
v_suppressElabErrors_2206_ = lean_ctor_get_uint8(v___y_2137_, sizeof(void*)*3 + 1);
v_ref_2207_ = l_Lean_replaceRef(v_option_2188_, v_ref_2204_);
lean_inc(v_currRecDepth_2203_);
lean_inc_ref(v_toCold_2202_);
v___x_2208_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2208_, 0, v_toCold_2202_);
lean_ctor_set(v___x_2208_, 1, v_currRecDepth_2203_);
lean_ctor_set(v___x_2208_, 2, v_ref_2207_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*3, v_diag_2205_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*3 + 1, v_suppressElabErrors_2206_);
lean_inc(v___x_2195_);
lean_inc(v_structName_2127_);
v___x_2209_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_2127_, v___x_2195_, v___y_2135_, v___y_2136_, v___x_2208_, v___y_2138_);
lean_dec_ref_known(v___x_2208_, 3);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
if (v_bool_2190_ == 0)
{
lean_object* v_fst_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v___x_2195_);
lean_del_object(v___x_2157_);
v_fst_2211_ = lean_ctor_get(v_a_2210_, 0);
lean_inc(v_fst_2211_);
lean_dec(v_a_2210_);
v___x_2212_ = lean_box(0);
lean_inc(v_value_2189_);
lean_inc(v_snd_2155_);
lean_inc(v_fst_2153_);
lean_inc(v_fst_2154_);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2197_, v_option_2188_, v_fst_2211_, v___x_2150_, v_fst_2154_, v_fst_2153_, v_snd_2155_, v_mkStructInst_2191_, v_seenFields_2192_, v_fields_2193_, v_value_2189_, v___x_2212_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v___y_2178_ = v___x_2213_;
goto v___jp_2177_;
}
else
{
lean_object* v_fst_2214_; lean_object* v_snd_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2241_; 
v_fst_2214_ = lean_ctor_get(v_a_2210_, 0);
v_snd_2215_ = lean_ctor_get(v_a_2210_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_a_2210_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2217_ = v_a_2210_;
v_isShared_2218_ = v_isSharedCheck_2241_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_snd_2215_);
lean_inc(v_fst_2214_);
lean_dec(v_a_2210_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2241_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_snd_2215_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l_Lean_ConstantInfo_type(v_a_2220_);
lean_dec(v_a_2220_);
v___x_2222_ = l_Lean_Expr_bindingBody_x21(v___x_2221_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5);
v___x_2224_ = lean_expr_eqv(v___x_2222_, v___x_2223_);
lean_dec_ref(v___x_2222_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7);
v___x_2226_ = l_Lean_MessageData_ofName(v___x_2195_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set_tag(v___x_2217_, 7);
lean_ctor_set(v___x_2217_, 1, v___x_2226_);
lean_ctor_set(v___x_2217_, 0, v___x_2225_);
v___x_2228_ = v___x_2217_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 7);
lean_ctor_set(v___x_2157_, 1, v___x_2229_);
lean_ctor_set(v___x_2157_, 0, v___x_2228_);
v___x_2231_ = v___x_2157_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_2187_, v___x_2231_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
lean_inc(v_value_2189_);
lean_inc(v_snd_2155_);
lean_inc(v_fst_2153_);
lean_inc(v_fst_2154_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2197_, v_option_2188_, v_fst_2214_, v___x_2150_, v_fst_2154_, v_fst_2153_, v_snd_2155_, v_mkStructInst_2191_, v_seenFields_2192_, v_fields_2193_, v_value_2189_, v_a_2233_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v___y_2178_ = v___x_2234_;
goto v___jp_2177_;
}
else
{
lean_object* v_a_2235_; 
lean_dec(v_fst_2214_);
lean_dec_ref(v_mkStructInst_2191_);
v_a_2235_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2232_, 1);
v_a_2174_ = v_a_2235_;
goto v___jp_2173_;
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_2217_);
lean_dec(v___x_2195_);
lean_del_object(v___x_2157_);
v___x_2238_ = lean_box(0);
lean_inc(v_value_2189_);
lean_inc(v_snd_2155_);
lean_inc(v_fst_2153_);
lean_inc(v_fst_2154_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2197_, v_option_2188_, v_fst_2214_, v___x_2150_, v_fst_2154_, v_fst_2153_, v_snd_2155_, v_mkStructInst_2191_, v_seenFields_2192_, v_fields_2193_, v_value_2189_, v___x_2238_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v___y_2178_ = v___x_2239_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2240_; 
lean_del_object(v___x_2217_);
lean_dec(v_fst_2214_);
lean_dec(v___x_2195_);
lean_dec_ref(v_mkStructInst_2191_);
lean_del_object(v___x_2157_);
v_a_2240_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2219_, 1);
v_a_2174_ = v_a_2240_;
goto v___jp_2173_;
}
}
}
}
else
{
lean_object* v_a_2242_; 
lean_dec(v___x_2195_);
lean_dec_ref(v_mkStructInst_2191_);
lean_del_object(v___x_2157_);
v_a_2242_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2209_, 1);
v_a_2174_ = v_a_2242_;
goto v___jp_2173_;
}
}
else
{
lean_object* v_a_2243_; 
lean_dec(v___x_2195_);
lean_dec_ref(v_mkStructInst_2191_);
lean_del_object(v___x_2157_);
v_a_2243_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2201_, 1);
v_a_2174_ = v_a_2243_;
goto v___jp_2173_;
}
}
else
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
lean_dec(v___x_2195_);
lean_dec_ref(v_mkStructInst_2191_);
lean_del_object(v___x_2157_);
v___x_2244_ = lean_array_get_size(v_snd_2155_);
v___x_2245_ = lean_nat_dec_eq(v___x_2244_, v___x_2149_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_inc(v_fst_2153_);
lean_inc(v_structName_2127_);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_2127_, v_fst_2153_, v_snd_2155_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 1);
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_box(0);
lean_inc(v_structName_2127_);
lean_inc(v_a_2186_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2186_, v_structName_2127_, v___x_2253_, v___x_2252_, v_seenFields_2192_, v_fields_2193_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v___y_2178_ = v___x_2254_;
goto v___jp_2177_;
}
}
}
else
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2246_, 1);
v_a_2174_ = v_a_2257_;
goto v___jp_2173_;
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_box(0);
lean_inc(v_snd_2155_);
lean_inc(v_fst_2154_);
lean_inc(v_fst_2153_);
lean_inc(v_structName_2127_);
lean_inc(v_a_2186_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2186_, v_structName_2127_, v___x_2258_, v_fst_2153_, v_fst_2154_, v_snd_2155_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v___y_2178_ = v___x_2259_;
goto v___jp_2177_;
}
}
v___jp_2159_:
{
if (v___y_2161_ == 0)
{
if (v_recover_2128_ == 0)
{
lean_object* v___x_2162_; 
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec(v_fst_2153_);
lean_dec(v_structName_2127_);
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2160_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v___y_2160_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref_known(v___x_2163_, 1);
v_fst_2141_ = v_fst_2153_;
v_fst_2142_ = v_fst_2154_;
v_snd_2143_ = v_snd_2155_;
goto v___jp_2140_;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec(v_fst_2153_);
lean_dec(v_structName_2127_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
else
{
lean_object* v___x_2172_; 
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec(v_fst_2153_);
lean_dec(v_structName_2127_);
v___x_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___y_2160_);
return v___x_2172_;
}
}
v___jp_2173_:
{
uint8_t v___x_2175_; 
v___x_2175_ = l_Lean_Exception_isInterrupt(v_a_2174_);
if (v___x_2175_ == 0)
{
uint8_t v___x_2176_; 
lean_inc_ref(v_a_2174_);
v___x_2176_ = l_Lean_Exception_isRuntime(v_a_2174_);
v___y_2160_ = v_a_2174_;
v___y_2161_ = v___x_2176_;
goto v___jp_2159_;
}
else
{
v___y_2160_ = v_a_2174_;
v___y_2161_ = v___x_2175_;
goto v___jp_2159_;
}
}
v___jp_2177_:
{
if (lean_obj_tag(v___y_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v_snd_2180_; lean_object* v_snd_2181_; lean_object* v_fst_2182_; lean_object* v_fst_2183_; lean_object* v_snd_2184_; 
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec(v_fst_2153_);
v_a_2179_ = lean_ctor_get(v___y_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___y_2178_, 1);
v_snd_2180_ = lean_ctor_get(v_a_2179_, 1);
lean_inc(v_snd_2180_);
lean_dec(v_a_2179_);
v_snd_2181_ = lean_ctor_get(v_snd_2180_, 1);
lean_inc(v_snd_2181_);
v_fst_2182_ = lean_ctor_get(v_snd_2180_, 0);
lean_inc(v_fst_2182_);
lean_dec(v_snd_2180_);
v_fst_2183_ = lean_ctor_get(v_snd_2181_, 0);
lean_inc(v_fst_2183_);
v_snd_2184_ = lean_ctor_get(v_snd_2181_, 1);
lean_inc(v_snd_2184_);
lean_dec(v_snd_2181_);
v_fst_2141_ = v_fst_2182_;
v_fst_2142_ = v_fst_2183_;
v_snd_2143_ = v_snd_2184_;
goto v___jp_2140_;
}
else
{
lean_object* v_a_2185_; 
v_a_2185_ = lean_ctor_get(v___y_2178_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___y_2178_, 1);
v_a_2174_ = v_a_2185_;
goto v___jp_2173_;
}
}
}
}
v___jp_2140_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; 
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_fst_2142_);
lean_ctor_set(v___x_2144_, 1, v_snd_2143_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_fst_2141_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2131_, v___x_2146_);
v_i_2131_ = v___x_2147_;
v_b_2132_ = v___x_2145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___boxed(lean_object* v_structName_2261_, lean_object* v_recover_2262_, lean_object* v_as_2263_, lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
uint8_t v_recover_boxed_2274_; size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_recover_boxed_2274_ = lean_unbox(v_recover_2262_);
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2261_, v_recover_boxed_2274_, v_as_2263_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v_as_2263_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0(lean_object* v_structName_2278_, uint8_t v_recover_2279_, lean_object* v_items_2280_, size_t v_sz_2281_, size_t v___x_2282_, lean_object* v___x_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_a_2292_; lean_object* v___x_2305_; 
lean_inc(v_structName_2278_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2278_, v_recover_2279_, v_items_2280_, v_sz_2281_, v___x_2282_, v___x_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_snd_2307_; lean_object* v_fst_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2385_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_snd_2307_ = lean_ctor_get(v_a_2306_, 1);
v_fst_2308_ = lean_ctor_get(v_a_2306_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_a_2306_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2310_ = v_a_2306_;
v_isShared_2311_ = v_isSharedCheck_2385_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_snd_2307_);
lean_inc(v_fst_2308_);
lean_dec(v_a_2306_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2385_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
if (lean_obj_tag(v_fst_2308_) == 0)
{
lean_object* v_snd_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2344_; 
v_snd_2312_ = lean_ctor_get(v_snd_2307_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_snd_2307_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_snd_2307_, 0);
lean_dec(v_unused_2345_);
v___x_2314_ = v_snd_2307_;
v_isShared_2315_ = v_isSharedCheck_2344_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_snd_2312_);
lean_dec(v_snd_2307_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2344_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_ref_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
v_ref_2316_ = lean_ctor_get(v___y_2288_, 2);
v___x_2317_ = 0;
v___x_2318_ = l_Lean_SourceInfo_fromRef(v_ref_2316_, v___x_2317_);
v___x_2319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2318_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 2);
lean_ctor_set(v___x_2314_, 1, v___x_2320_);
lean_ctor_set(v___x_2314_, 0, v___x_2318_);
v___x_2322_ = v___x_2314_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2324_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2318_, 5);
v___x_2325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2318_);
lean_ctor_set(v___x_2325_, 1, v___x_2323_);
lean_ctor_set(v___x_2325_, 2, v___x_2324_);
v___x_2326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2328_ = l_Lean_Syntax_SepArray_ofElems(v___x_2327_, v_snd_2312_);
lean_dec(v_snd_2312_);
v___x_2329_ = l_Array_append___redArg(v___x_2324_, v___x_2328_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2318_);
lean_ctor_set(v___x_2330_, 1, v___x_2323_);
lean_ctor_set(v___x_2330_, 2, v___x_2329_);
v___x_2331_ = l_Lean_Syntax_node1(v___x_2318_, v___x_2326_, v___x_2330_);
v___x_2332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_2325_);
v___x_2333_ = l_Lean_Syntax_node1(v___x_2318_, v___x_2332_, v___x_2325_);
v___x_2334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 2);
lean_ctor_set(v___x_2310_, 1, v___x_2334_);
lean_ctor_set(v___x_2310_, 0, v___x_2318_);
v___x_2336_ = v___x_2310_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_inc(v_structName_2278_);
v___x_2337_ = l_Lean_mkCIdent(v_structName_2278_);
lean_inc_n(v___x_2318_, 2);
v___x_2338_ = l_Lean_Syntax_node2(v___x_2318_, v___x_2323_, v___x_2336_, v___x_2337_);
v___x_2339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2318_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_Syntax_node6(v___x_2318_, v___x_2319_, v___x_2322_, v___x_2325_, v___x_2331_, v___x_2333_, v___x_2338_, v___x_2340_);
v_a_2292_ = v___x_2341_;
goto v___jp_2291_;
}
}
}
}
else
{
lean_object* v_snd_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2383_; 
v_snd_2346_ = lean_ctor_get(v_snd_2307_, 1);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_snd_2307_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v_snd_2307_, 0);
lean_dec(v_unused_2384_);
v___x_2348_ = v_snd_2307_;
v_isShared_2349_ = v_isSharedCheck_2383_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_snd_2346_);
lean_dec(v_snd_2307_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2383_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_val_2350_; lean_object* v_ref_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v_val_2350_ = lean_ctor_get(v_fst_2308_, 0);
lean_inc(v_val_2350_);
lean_dec_ref_known(v_fst_2308_, 1);
v_ref_2351_ = lean_ctor_get(v___y_2288_, 2);
v___x_2352_ = 0;
v___x_2353_ = l_Lean_SourceInfo_fromRef(v_ref_2351_, v___x_2352_);
v___x_2354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2353_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 2);
lean_ctor_set(v___x_2348_, 1, v___x_2355_);
lean_ctor_set(v___x_2348_, 0, v___x_2353_);
v___x_2357_ = v___x_2348_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
lean_inc_n(v___x_2353_, 2);
v___x_2359_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2358_, v_val_2350_);
v___x_2360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 2);
lean_ctor_set(v___x_2310_, 1, v___x_2360_);
lean_ctor_set(v___x_2310_, 0, v___x_2353_);
v___x_2362_ = v___x_2310_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_inc_n(v___x_2353_, 8);
v___x_2363_ = l_Lean_Syntax_node2(v___x_2353_, v___x_2358_, v___x_2359_, v___x_2362_);
v___x_2364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_2366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2367_ = l_Lean_Syntax_SepArray_ofElems(v___x_2366_, v_snd_2346_);
lean_dec(v_snd_2346_);
v___x_2368_ = l_Array_append___redArg(v___x_2365_, v___x_2367_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2353_);
lean_ctor_set(v___x_2369_, 1, v___x_2358_);
lean_ctor_set(v___x_2369_, 2, v___x_2368_);
v___x_2370_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2364_, v___x_2369_);
v___x_2371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_2372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2353_);
lean_ctor_set(v___x_2372_, 1, v___x_2358_);
lean_ctor_set(v___x_2372_, 2, v___x_2365_);
v___x_2373_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2371_, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_2375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2353_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
lean_inc(v_structName_2278_);
v___x_2376_ = l_Lean_mkCIdent(v_structName_2278_);
v___x_2377_ = l_Lean_Syntax_node2(v___x_2353_, v___x_2358_, v___x_2375_, v___x_2376_);
v___x_2378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2353_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = l_Lean_Syntax_node6(v___x_2353_, v___x_2354_, v___x_2357_, v___x_2363_, v___x_2370_, v___x_2373_, v___x_2377_, v___x_2379_);
v_a_2292_ = v___x_2380_;
goto v___jp_2291_;
}
}
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_structName_2278_);
v_a_2386_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2305_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2305_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = l_Lean_mkConst(v_structName_2278_, v___x_2293_);
v___x_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
v___x_2296_ = 1;
v___x_2297_ = lean_box(0);
v___x_2298_ = lean_box(v___x_2296_);
v___x_2299_ = lean_box(v___x_2296_);
v___x_2300_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2300_, 0, v_a_2292_);
lean_closure_set(v___x_2300_, 1, v___x_2295_);
lean_closure_set(v___x_2300_, 2, v___x_2298_);
lean_closure_set(v___x_2300_, 3, v___x_2299_);
lean_closure_set(v___x_2300_, 4, v___x_2297_);
v___x_2301_ = 1;
v___x_2302_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2300_, v___x_2301_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_a_2303_, v___y_2287_);
return v___x_2304_;
}
else
{
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0___boxed(lean_object* v_structName_2394_, lean_object* v_recover_2395_, lean_object* v_items_2396_, lean_object* v_sz_2397_, lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
uint8_t v_recover_boxed_2407_; size_t v_sz_boxed_2408_; size_t v___x_50443__boxed_2409_; lean_object* v_res_2410_; 
v_recover_boxed_2407_ = lean_unbox(v_recover_2395_);
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2397_);
lean_dec(v_sz_2397_);
v___x_50443__boxed_2409_ = lean_unbox_usize(v___x_2398_);
lean_dec(v___x_2398_);
v_res_2410_ = l_Lean_Elab_Tactic_elabConfig___lam__0(v_structName_2394_, v_recover_boxed_2407_, v_items_2396_, v_sz_boxed_2408_, v___x_50443__boxed_2409_, v___x_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_items_2396_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_env_2416_; lean_object* v___x_2417_; lean_object* v_toCold_2418_; lean_object* v_mctx_2419_; lean_object* v_options_2420_; lean_object* v_currNamespace_2421_; lean_object* v_openDecls_2422_; lean_object* v___x_2423_; lean_object* v_ngen_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_env_2416_);
lean_dec(v___x_2415_);
v___x_2417_ = lean_st_ref_get(v___y_2411_);
v_toCold_2418_ = lean_ctor_get(v___y_2412_, 0);
v_mctx_2419_ = lean_ctor_get(v___x_2417_, 0);
lean_inc_ref(v_mctx_2419_);
lean_dec(v___x_2417_);
v_options_2420_ = lean_ctor_get(v_toCold_2418_, 2);
v_currNamespace_2421_ = lean_ctor_get(v_toCold_2418_, 4);
v_openDecls_2422_ = lean_ctor_get(v_toCold_2418_, 5);
v___x_2423_ = lean_st_ref_get(v___y_2413_);
v_ngen_2424_ = lean_ctor_get(v___x_2423_, 2);
lean_inc_ref(v_ngen_2424_);
lean_dec(v___x_2423_);
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_2422_);
lean_inc(v_currNamespace_2421_);
lean_inc_ref(v_options_2420_);
v___x_2427_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2427_, 0, v_env_2416_);
lean_ctor_set(v___x_2427_, 1, v___x_2425_);
lean_ctor_set(v___x_2427_, 2, v___x_2426_);
lean_ctor_set(v___x_2427_, 3, v_mctx_2419_);
lean_ctor_set(v___x_2427_, 4, v_options_2420_);
lean_ctor_set(v___x_2427_, 5, v_currNamespace_2421_);
lean_ctor_set(v___x_2427_, 6, v_openDecls_2422_);
lean_ctor_set(v___x_2427_, 7, v_ngen_2424_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v_toCold_2442_; lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2467_; 
v___x_2441_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2437_, v___y_2438_, v___y_2439_);
v_toCold_2442_ = lean_ctor_get(v___y_2438_, 0);
v_a_2443_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2445_ = v___x_2441_;
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2441_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_fileMap_2447_; lean_object* v_env_2448_; lean_object* v_mctx_2449_; lean_object* v_options_2450_; lean_object* v_currNamespace_2451_; lean_object* v_openDecls_2452_; lean_object* v_ngen_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2464_; 
v_fileMap_2447_ = lean_ctor_get(v_toCold_2442_, 1);
v_env_2448_ = lean_ctor_get(v_a_2443_, 0);
v_mctx_2449_ = lean_ctor_get(v_a_2443_, 3);
v_options_2450_ = lean_ctor_get(v_a_2443_, 4);
v_currNamespace_2451_ = lean_ctor_get(v_a_2443_, 5);
v_openDecls_2452_ = lean_ctor_get(v_a_2443_, 6);
v_ngen_2453_ = lean_ctor_get(v_a_2443_, 7);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_a_2443_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; lean_object* v_unused_2466_; 
v_unused_2465_ = lean_ctor_get(v_a_2443_, 2);
lean_dec(v_unused_2465_);
v_unused_2466_ = lean_ctor_get(v_a_2443_, 1);
lean_dec(v_unused_2466_);
v___x_2455_ = v_a_2443_;
v_isShared_2456_ = v_isSharedCheck_2464_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_ngen_2453_);
lean_inc(v_openDecls_2452_);
lean_inc(v_currNamespace_2451_);
lean_inc(v_options_2450_);
lean_inc(v_mctx_2449_);
lean_inc(v_env_2448_);
lean_dec(v_a_2443_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2464_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = lean_box(0);
lean_inc_ref(v_fileMap_2447_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 2, v_fileMap_2447_);
lean_ctor_set(v___x_2455_, 1, v___x_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_env_2448_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_fileMap_2447_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_mctx_2449_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_options_2450_);
lean_ctor_set(v_reuseFailAlloc_2463_, 5, v_currNamespace_2451_);
lean_ctor_set(v_reuseFailAlloc_2463_, 6, v_openDecls_2452_);
lean_ctor_set(v_reuseFailAlloc_2463_, 7, v_ngen_2453_);
v___x_2459_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2461_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2459_);
v___x_2461_ = v___x_2445_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11___boxed(lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2493_; 
v___x_2483_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_a_2484_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2489_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed(lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(lean_object* v___x_2502_, lean_object* v_ctx_x3f_2503_, size_t v_sz_2504_, size_t v_i_2505_, lean_object* v_bs_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_lt(v_i_2505_, v_sz_2504_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
lean_dec_ref(v_ctx_x3f_2503_);
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_bs_2506_);
return v___x_2515_;
}
else
{
lean_object* v_assignment_2516_; lean_object* v___x_2517_; 
v_assignment_2516_ = lean_ctor_get(v___x_2502_, 0);
lean_inc_ref(v_ctx_x3f_2503_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
v___x_2517_ = lean_apply_7(v_ctx_x3f_2503_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, lean_box(0));
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v_v_2519_; lean_object* v___x_2520_; lean_object* v_bs_x27_2521_; lean_object* v_a_2523_; lean_object* v_tree_2528_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v_v_2519_ = lean_array_uget(v_bs_2506_, v_i_2505_);
v___x_2520_ = lean_unsigned_to_nat(0u);
v_bs_x27_2521_ = lean_array_uset(v_bs_2506_, v_i_2505_, v___x_2520_);
v_tree_2528_ = l_Lean_Elab_InfoTree_substitute(v_v_2519_, v_assignment_2516_);
if (lean_obj_tag(v_a_2518_) == 0)
{
v_a_2523_ = v_tree_2528_;
goto v___jp_2522_;
}
else
{
lean_object* v_val_2529_; lean_object* v___x_2530_; 
v_val_2529_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_val_2529_);
lean_dec_ref_known(v_a_2518_, 1);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_val_2529_);
lean_ctor_set(v___x_2530_, 1, v_tree_2528_);
v_a_2523_ = v___x_2530_;
goto v___jp_2522_;
}
v___jp_2522_:
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2505_, v___x_2524_);
v___x_2526_ = lean_array_uset(v_bs_x27_2521_, v_i_2505_, v_a_2523_);
v_i_2505_ = v___x_2525_;
v_bs_2506_ = v___x_2526_;
goto _start;
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_bs_2506_);
lean_dec_ref(v_ctx_x3f_2503_);
v_a_2531_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2517_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2517_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27___boxed(lean_object* v___x_2539_, lean_object* v_ctx_x3f_2540_, lean_object* v_sz_2541_, lean_object* v_i_2542_, lean_object* v_bs_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
size_t v_sz_boxed_2551_; size_t v_i_boxed_2552_; lean_object* v_res_2553_; 
v_sz_boxed_2551_ = lean_unbox_usize(v_sz_2541_);
lean_dec(v_sz_2541_);
v_i_boxed_2552_ = lean_unbox_usize(v_i_2542_);
lean_dec(v_i_2542_);
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2539_, v_ctx_x3f_2540_, v_sz_boxed_2551_, v_i_boxed_2552_, v_bs_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v___x_2539_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(lean_object* v___x_2554_, lean_object* v_ctx_x3f_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
if (lean_obj_tag(v_x_2556_) == 0)
{
lean_object* v_cs_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2590_; 
v_cs_2564_ = lean_ctor_get(v_x_2556_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_x_2556_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2566_ = v_x_2556_;
v_isShared_2567_ = v_isSharedCheck_2590_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_cs_2564_);
lean_dec(v_x_2556_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2590_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
size_t v_sz_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
v_sz_2568_ = lean_array_size(v_cs_2564_);
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2554_, v_ctx_x3f_2555_, v_sz_2568_, v___x_2569_, v_cs_2564_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2581_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2581_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2581_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v_a_2571_);
v___x_2576_ = v___x_2566_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2576_);
v___x_2578_ = v___x_2573_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_del_object(v___x_2566_);
v_a_2582_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2570_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2570_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
else
{
lean_object* v_vs_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2617_; 
v_vs_2591_ = lean_ctor_get(v_x_2556_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_x_2556_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2593_ = v_x_2556_;
v_isShared_2594_ = v_isSharedCheck_2617_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_vs_2591_);
lean_dec(v_x_2556_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2617_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
size_t v_sz_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v_sz_2595_ = lean_array_size(v_vs_2591_);
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2554_, v_ctx_x3f_2555_, v_sz_2595_, v___x_2596_, v_vs_2591_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2608_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2608_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2608_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v_a_2598_);
v___x_2603_ = v___x_2593_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2605_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2603_);
v___x_2605_ = v___x_2600_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_del_object(v___x_2593_);
v_a_2609_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2597_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2597_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(lean_object* v___x_2618_, lean_object* v_ctx_x3f_2619_, size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_bs_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_usize_dec_lt(v_i_2621_, v_sz_2620_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v_ctx_x3f_2619_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v_bs_2622_);
return v___x_2631_;
}
else
{
lean_object* v_v_2632_; lean_object* v___x_2633_; 
v_v_2632_ = lean_array_uget_borrowed(v_bs_2622_, v_i_2621_);
lean_inc(v_v_2632_);
lean_inc_ref(v_ctx_x3f_2619_);
v___x_2633_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2618_, v_ctx_x3f_2619_, v_v_2632_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; lean_object* v_bs_x27_2636_; size_t v___x_2637_; size_t v___x_2638_; lean_object* v___x_2639_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = lean_unsigned_to_nat(0u);
v_bs_x27_2636_ = lean_array_uset(v_bs_2622_, v_i_2621_, v___x_2635_);
v___x_2637_ = ((size_t)1ULL);
v___x_2638_ = lean_usize_add(v_i_2621_, v___x_2637_);
v___x_2639_ = lean_array_uset(v_bs_x27_2636_, v_i_2621_, v_a_2634_);
v_i_2621_ = v___x_2638_;
v_bs_2622_ = v___x_2639_;
goto _start;
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v_bs_2622_);
lean_dec_ref(v_ctx_x3f_2619_);
v_a_2641_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2633_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2633_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28___boxed(lean_object* v___x_2649_, lean_object* v_ctx_x3f_2650_, lean_object* v_sz_2651_, lean_object* v_i_2652_, lean_object* v_bs_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
size_t v_sz_boxed_2661_; size_t v_i_boxed_2662_; lean_object* v_res_2663_; 
v_sz_boxed_2661_ = lean_unbox_usize(v_sz_2651_);
lean_dec(v_sz_2651_);
v_i_boxed_2662_ = lean_unbox_usize(v_i_2652_);
lean_dec(v_i_2652_);
v_res_2663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2649_, v_ctx_x3f_2650_, v_sz_boxed_2661_, v_i_boxed_2662_, v_bs_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v___x_2649_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26___boxed(lean_object* v___x_2664_, lean_object* v_ctx_x3f_2665_, lean_object* v_x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2664_, v_ctx_x3f_2665_, v_x_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec_ref(v___x_2664_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(lean_object* v___x_2675_, lean_object* v_ctx_x3f_2676_, lean_object* v_t_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_root_2685_; lean_object* v_tail_2686_; lean_object* v_size_2687_; size_t v_shift_2688_; lean_object* v_tailOff_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2725_; 
v_root_2685_ = lean_ctor_get(v_t_2677_, 0);
v_tail_2686_ = lean_ctor_get(v_t_2677_, 1);
v_size_2687_ = lean_ctor_get(v_t_2677_, 2);
v_shift_2688_ = lean_ctor_get_usize(v_t_2677_, 4);
v_tailOff_2689_ = lean_ctor_get(v_t_2677_, 3);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_t_2677_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2691_ = v_t_2677_;
v_isShared_2692_ = v_isSharedCheck_2725_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_tailOff_2689_);
lean_inc(v_size_2687_);
lean_inc(v_tail_2686_);
lean_inc(v_root_2685_);
lean_dec(v_t_2677_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2725_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; 
lean_inc_ref(v_ctx_x3f_2676_);
v___x_2693_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2675_, v_ctx_x3f_2676_, v_root_2685_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; size_t v_sz_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v_sz_2695_ = lean_array_size(v_tail_2686_);
v___x_2696_ = ((size_t)0ULL);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2675_, v_ctx_x3f_2676_, v_sz_2695_, v___x_2696_, v_tail_2686_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2708_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v_a_2698_);
lean_ctor_set(v___x_2691_, 0, v_a_2694_);
v___x_2703_ = v___x_2691_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2694_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_a_2698_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_size_2687_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_tailOff_2689_);
lean_ctor_set_usize(v_reuseFailAlloc_2707_, 4, v_shift_2688_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2694_);
lean_del_object(v___x_2691_);
lean_dec(v_tailOff_2689_);
lean_dec(v_size_2687_);
v_a_2709_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2697_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2697_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_del_object(v___x_2691_);
lean_dec(v_tailOff_2689_);
lean_dec(v_size_2687_);
lean_dec_ref(v_tail_2686_);
lean_dec_ref(v_ctx_x3f_2676_);
v_a_2717_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2693_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2693_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22___boxed(lean_object* v___x_2726_, lean_object* v_ctx_x3f_2727_, lean_object* v_t_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v___x_2726_, v_ctx_x3f_2727_, v_t_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec_ref(v___x_2726_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(lean_object* v___y_2737_, lean_object* v_ctx_x3f_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v_a_2744_, lean_object* v_a_x3f_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v_infoState_2748_; lean_object* v_trees_2749_; lean_object* v___x_2750_; 
v___x_2747_ = lean_st_ref_get(v___y_2737_);
v_infoState_2748_ = lean_ctor_get(v___x_2747_, 7);
lean_inc_ref(v_infoState_2748_);
lean_dec(v___x_2747_);
v_trees_2749_ = lean_ctor_get(v_infoState_2748_, 2);
lean_inc_ref(v_trees_2749_);
v___x_2750_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v_infoState_2748_, v_ctx_x3f_2738_, v_trees_2749_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2737_);
lean_dec_ref(v_infoState_2748_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2789_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2789_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2789_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v_infoState_2756_; lean_object* v_env_2757_; lean_object* v_nextMacroScope_2758_; lean_object* v_ngen_2759_; lean_object* v_auxDeclNGen_2760_; lean_object* v_traceState_2761_; lean_object* v_cache_2762_; lean_object* v_messages_2763_; lean_object* v_snapshotTasks_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2788_; 
v___x_2755_ = lean_st_ref_take(v___y_2737_);
v_infoState_2756_ = lean_ctor_get(v___x_2755_, 7);
v_env_2757_ = lean_ctor_get(v___x_2755_, 0);
v_nextMacroScope_2758_ = lean_ctor_get(v___x_2755_, 1);
v_ngen_2759_ = lean_ctor_get(v___x_2755_, 2);
v_auxDeclNGen_2760_ = lean_ctor_get(v___x_2755_, 3);
v_traceState_2761_ = lean_ctor_get(v___x_2755_, 4);
v_cache_2762_ = lean_ctor_get(v___x_2755_, 5);
v_messages_2763_ = lean_ctor_get(v___x_2755_, 6);
v_snapshotTasks_2764_ = lean_ctor_get(v___x_2755_, 8);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2766_ = v___x_2755_;
v_isShared_2767_ = v_isSharedCheck_2788_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_snapshotTasks_2764_);
lean_inc(v_infoState_2756_);
lean_inc(v_messages_2763_);
lean_inc(v_cache_2762_);
lean_inc(v_traceState_2761_);
lean_inc(v_auxDeclNGen_2760_);
lean_inc(v_ngen_2759_);
lean_inc(v_nextMacroScope_2758_);
lean_inc(v_env_2757_);
lean_dec(v___x_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2788_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint8_t v_enabled_2768_; lean_object* v_assignment_2769_; lean_object* v_lazyAssignment_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2786_; 
v_enabled_2768_ = lean_ctor_get_uint8(v_infoState_2756_, sizeof(void*)*3);
v_assignment_2769_ = lean_ctor_get(v_infoState_2756_, 0);
v_lazyAssignment_2770_ = lean_ctor_get(v_infoState_2756_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_infoState_2756_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v_infoState_2756_, 2);
lean_dec(v_unused_2787_);
v___x_2772_ = v_infoState_2756_;
v_isShared_2773_ = v_isSharedCheck_2786_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_lazyAssignment_2770_);
lean_inc(v_assignment_2769_);
lean_dec(v_infoState_2756_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2786_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = l_Lean_PersistentArray_append___redArg(v_a_2744_, v_a_2751_);
lean_dec(v_a_2751_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 2, v___x_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_assignment_2769_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_lazyAssignment_2770_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v___x_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2785_, sizeof(void*)*3, v_enabled_2768_);
v___x_2776_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 7, v___x_2776_);
v___x_2778_ = v___x_2766_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_env_2757_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_nextMacroScope_2758_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v_ngen_2759_);
lean_ctor_set(v_reuseFailAlloc_2784_, 3, v_auxDeclNGen_2760_);
lean_ctor_set(v_reuseFailAlloc_2784_, 4, v_traceState_2761_);
lean_ctor_set(v_reuseFailAlloc_2784_, 5, v_cache_2762_);
lean_ctor_set(v_reuseFailAlloc_2784_, 6, v_messages_2763_);
lean_ctor_set(v_reuseFailAlloc_2784_, 7, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2784_, 8, v_snapshotTasks_2764_);
v___x_2778_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2779_ = lean_st_ref_put(v___y_2737_, v___x_2778_);
v___x_2780_ = lean_box(0);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2780_);
v___x_2782_ = v___x_2753_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v_a_2744_);
v_a_2790_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2750_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2750_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v___y_2798_, lean_object* v_ctx_x3f_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v_a_2805_, lean_object* v_a_x3f_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2798_, v_ctx_x3f_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v_a_2805_, v_a_x3f_2806_);
lean_dec(v_a_x3f_2806_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2798_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; lean_object* v_infoState_2812_; lean_object* v_trees_2813_; lean_object* v___x_2814_; lean_object* v_infoState_2815_; lean_object* v_env_2816_; lean_object* v_nextMacroScope_2817_; lean_object* v_ngen_2818_; lean_object* v_auxDeclNGen_2819_; lean_object* v_traceState_2820_; lean_object* v_cache_2821_; lean_object* v_messages_2822_; lean_object* v_snapshotTasks_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2846_; 
v___x_2811_ = lean_st_ref_get(v___y_2809_);
v_infoState_2812_ = lean_ctor_get(v___x_2811_, 7);
lean_inc_ref(v_infoState_2812_);
lean_dec(v___x_2811_);
v_trees_2813_ = lean_ctor_get(v_infoState_2812_, 2);
lean_inc_ref(v_trees_2813_);
lean_dec_ref(v_infoState_2812_);
v___x_2814_ = lean_st_ref_take(v___y_2809_);
v_infoState_2815_ = lean_ctor_get(v___x_2814_, 7);
v_env_2816_ = lean_ctor_get(v___x_2814_, 0);
v_nextMacroScope_2817_ = lean_ctor_get(v___x_2814_, 1);
v_ngen_2818_ = lean_ctor_get(v___x_2814_, 2);
v_auxDeclNGen_2819_ = lean_ctor_get(v___x_2814_, 3);
v_traceState_2820_ = lean_ctor_get(v___x_2814_, 4);
v_cache_2821_ = lean_ctor_get(v___x_2814_, 5);
v_messages_2822_ = lean_ctor_get(v___x_2814_, 6);
v_snapshotTasks_2823_ = lean_ctor_get(v___x_2814_, 8);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2825_ = v___x_2814_;
v_isShared_2826_ = v_isSharedCheck_2846_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_snapshotTasks_2823_);
lean_inc(v_infoState_2815_);
lean_inc(v_messages_2822_);
lean_inc(v_cache_2821_);
lean_inc(v_traceState_2820_);
lean_inc(v_auxDeclNGen_2819_);
lean_inc(v_ngen_2818_);
lean_inc(v_nextMacroScope_2817_);
lean_inc(v_env_2816_);
lean_dec(v___x_2814_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2846_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
uint8_t v_enabled_2827_; lean_object* v_assignment_2828_; lean_object* v_lazyAssignment_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2844_; 
v_enabled_2827_ = lean_ctor_get_uint8(v_infoState_2815_, sizeof(void*)*3);
v_assignment_2828_ = lean_ctor_get(v_infoState_2815_, 0);
v_lazyAssignment_2829_ = lean_ctor_get(v_infoState_2815_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_infoState_2815_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v_infoState_2815_, 2);
lean_dec(v_unused_2845_);
v___x_2831_ = v_infoState_2815_;
v_isShared_2832_ = v_isSharedCheck_2844_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_lazyAssignment_2829_);
lean_inc(v_assignment_2828_);
lean_dec(v_infoState_2815_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2844_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2833_ = lean_unsigned_to_nat(32u);
v___x_2834_ = lean_mk_empty_array_with_capacity(v___x_2833_);
lean_dec_ref(v___x_2834_);
v___x_2835_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 2, v___x_2835_);
v___x_2837_ = v___x_2831_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_assignment_2828_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_lazyAssignment_2829_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v___x_2835_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, sizeof(void*)*3, v_enabled_2827_);
v___x_2837_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 7, v___x_2837_);
v___x_2839_ = v___x_2825_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_env_2816_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_nextMacroScope_2817_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_ngen_2818_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_auxDeclNGen_2819_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_traceState_2820_);
lean_ctor_set(v_reuseFailAlloc_2842_, 5, v_cache_2821_);
lean_ctor_set(v_reuseFailAlloc_2842_, 6, v_messages_2822_);
lean_ctor_set(v_reuseFailAlloc_2842_, 7, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2842_, 8, v_snapshotTasks_2823_);
v___x_2839_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_st_ref_put(v___y_2809_, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_trees_2813_);
return v___x_2841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg___boxed(lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2847_);
lean_dec(v___y_2847_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(lean_object* v_x_2850_, lean_object* v_ctx_x3f_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v_infoState_2860_; uint8_t v_enabled_2861_; 
v___x_2859_ = lean_st_ref_get(v___y_2857_);
v_infoState_2860_ = lean_ctor_get(v___x_2859_, 7);
lean_inc_ref(v_infoState_2860_);
lean_dec(v___x_2859_);
v_enabled_2861_ = lean_ctor_get_uint8(v_infoState_2860_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2860_);
if (v_enabled_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref(v_ctx_x3f_2851_);
lean_inc(v___y_2857_);
lean_inc_ref(v___y_2856_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
v___x_2862_ = lean_apply_7(v_x_2850_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, lean_box(0));
return v___x_2862_;
}
else
{
lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v_r_2865_; 
v___x_2863_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2857_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2863_);
lean_inc(v___y_2857_);
lean_inc_ref(v___y_2856_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
v_r_2865_ = lean_apply_7(v_x_2850_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, lean_box(0));
if (lean_obj_tag(v_r_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2890_; 
v_a_2866_ = lean_ctor_get(v_r_2865_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_r_2865_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2868_ = v_r_2865_;
v_isShared_2869_ = v_isSharedCheck_2890_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v_r_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2890_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
lean_inc(v_a_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 1);
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2857_, v_ctx_x3f_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v_a_2864_, v___x_2871_);
lean_dec_ref(v___x_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; 
v_unused_2880_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2880_);
v___x_2874_ = v___x_2872_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v___x_2872_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v_a_2866_);
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2866_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_a_2866_);
v_a_2881_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2872_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2872_);
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
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_a_2891_ = lean_ctor_get(v_r_2865_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v_r_2865_, 1);
v___x_2892_ = lean_box(0);
v___x_2893_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2857_, v_ctx_x3f_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v_a_2864_, v___x_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v___x_2893_, 0);
lean_dec(v_unused_2901_);
v___x_2895_ = v___x_2893_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_dec(v___x_2893_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 1);
lean_ctor_set(v___x_2895_, 0, v_a_2891_);
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2891_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2891_);
v_a_2902_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2893_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2893_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___boxed(lean_object* v_x_2910_, lean_object* v_ctx_x3f_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2910_, v_ctx_x3f_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___f_2929_; lean_object* v___x_2930_; 
v___f_2929_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0));
v___x_2930_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2921_, v___f_2929_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___boxed(lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(lean_object* v_00_u03b1_2940_, lean_object* v_x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed(lean_object* v_00_u03b1_2950_, lean_object* v_x_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(v_00_u03b1_2950_, v_x_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2959_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__1(void){
_start:
{
lean_object* v_fields_2962_; lean_object* v_seenFields_2963_; lean_object* v___x_2964_; 
v_fields_2962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v_seenFields_2963_ = l_Lean_NameSet_empty;
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_seenFields_2963_);
lean_ctor_set(v___x_2964_, 1, v_fields_2962_);
return v___x_2964_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__2(void){
_start:
{
lean_object* v___x_2965_; lean_object* v_source_x3f_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__1, &l_Lean_Elab_Tactic_elabConfig___closed__1_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__1);
v_source_x3f_2966_ = lean_box(0);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_source_x3f_2966_);
lean_ctor_set(v___x_2967_, 1, v___x_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t v_recover_2970_, lean_object* v_structName_2971_, lean_object* v_items_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; size_t v_sz_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___f_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2980_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3);
v___x_2981_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___closed__0));
v___x_2982_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__2, &l_Lean_Elab_Tactic_elabConfig___closed__2_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__2);
v_sz_2983_ = lean_array_size(v_items_2972_);
v___x_2984_ = lean_box(v_recover_2970_);
v___x_2985_ = lean_box_usize(v_sz_2983_);
v___x_2986_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___boxed__const__1));
v___f_2987_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabConfig___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2987_, 0, v_structName_2971_);
lean_closure_set(v___f_2987_, 1, v___x_2984_);
lean_closure_set(v___f_2987_, 2, v_items_2972_);
lean_closure_set(v___f_2987_, 3, v___x_2985_);
lean_closure_set(v___f_2987_, 4, v___x_2986_);
lean_closure_set(v___f_2987_, 5, v___x_2982_);
v___x_2988_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed), 9, 2);
lean_closure_set(v___x_2988_, 0, lean_box(0));
lean_closure_set(v___x_2988_, 1, v___f_2987_);
v___x_2989_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed), 11, 4);
lean_closure_set(v___x_2989_, 0, lean_box(0));
lean_closure_set(v___x_2989_, 1, v___x_2980_);
lean_closure_set(v___x_2989_, 2, v___x_2981_);
lean_closure_set(v___x_2989_, 3, v___x_2988_);
v___x_2990_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v___x_2989_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___boxed(lean_object* v_recover_2991_, lean_object* v_structName_2992_, lean_object* v_items_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
uint8_t v_recover_boxed_3001_; lean_object* v_res_3002_; 
v_recover_boxed_3001_ = lean_unbox(v_recover_2991_);
v_res_3002_ = l_Lean_Elab_Tactic_elabConfig(v_recover_boxed_3001_, v_structName_2992_, v_items_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(lean_object* v_00_u03b1_3003_, lean_object* v_ref_3004_, lean_object* v_msg_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_3004_, v_msg_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___boxed(lean_object* v_00_u03b1_3014_, lean_object* v_ref_3015_, lean_object* v_msg_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(v_00_u03b1_3014_, v_ref_3015_, v_msg_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v_ref_3015_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(lean_object* v_t_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_3025_, v___y_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___boxed(lean_object* v_t_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(v_t_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(lean_object* v_00_u03b1_3043_, lean_object* v_constName_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3053_, lean_object* v_constName_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(v_00_u03b1_3053_, v_constName_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(lean_object* v_00_u03b1_3063_, lean_object* v_msg_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3073_, lean_object* v_msg_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(v_00_u03b1_3073_, v_msg_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_3086_, v___y_3087_, v___y_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___boxed(lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___boxed(lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(lean_object* v_00_u03b1_3115_, lean_object* v_x_3116_, lean_object* v_ctx_x3f_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_3116_, v_ctx_x3f_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3126_, lean_object* v_x_3127_, lean_object* v_ctx_x3f_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(v_00_u03b1_3126_, v_x_3127_, v_ctx_x3f_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(lean_object* v_ref_3137_, lean_object* v_msgData_3138_, uint8_t v_severity_3139_, uint8_t v_isSilent_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_3137_, v_msgData_3138_, v_severity_3139_, v_isSilent_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___boxed(lean_object* v_ref_3149_, lean_object* v_msgData_3150_, lean_object* v_severity_3151_, lean_object* v_isSilent_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v_severity_boxed_3160_; uint8_t v_isSilent_boxed_3161_; lean_object* v_res_3162_; 
v_severity_boxed_3160_ = lean_unbox(v_severity_3151_);
v_isSilent_boxed_3161_ = lean_unbox(v_isSilent_3152_);
v_res_3162_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(v_ref_3149_, v_msgData_3150_, v_severity_boxed_3160_, v_isSilent_boxed_3161_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v_ref_3149_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(lean_object* v_00_u03b1_3163_, lean_object* v_ref_3164_, lean_object* v_constName_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_3164_, v_constName_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b1_3174_, lean_object* v_ref_3175_, lean_object* v_constName_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(v_00_u03b1_3174_, v_ref_3175_, v_constName_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v_ref_3175_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(lean_object* v_msgData_3185_, lean_object* v_macroStack_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_3185_, v_macroStack_3186_, v___y_3191_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___boxed(lean_object* v_msgData_3195_, lean_object* v_macroStack_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(v_msgData_3195_, v_macroStack_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(lean_object* v_00_u03b1_3205_, lean_object* v_ref_3206_, lean_object* v_msg_3207_, lean_object* v_declHint_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_3206_, v_msg_3207_, v_declHint_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___boxed(lean_object* v_00_u03b1_3217_, lean_object* v_ref_3218_, lean_object* v_msg_3219_, lean_object* v_declHint_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(v_00_u03b1_3217_, v_ref_3218_, v_msg_3219_, v_declHint_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v_ref_3218_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(lean_object* v_msg_3229_, lean_object* v_declHint_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_3229_, v_declHint_3230_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___boxed(lean_object* v_msg_3239_, lean_object* v_declHint_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(v_msg_3239_, v_declHint_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3248_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11));
v___x_3282_ = l_String_toRawSubstring_x27(v___x_3281_);
return v___x_3282_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18));
v___x_3299_ = l_String_toRawSubstring_x27(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21));
v___x_3304_ = l_String_toRawSubstring_x27(v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31));
v___x_3329_ = l_String_toRawSubstring_x27(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39));
v___x_3351_ = l_String_toRawSubstring_x27(v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48));
v___x_3374_ = l_String_toRawSubstring_x27(v___x_3373_);
return v___x_3374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3385_ = l_String_toRawSubstring_x27(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71));
v___x_3429_ = l_String_toRawSubstring_x27(v___x_3428_);
return v___x_3429_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77));
v___x_3441_ = l_String_toRawSubstring_x27(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83));
v___x_3456_ = l_String_toRawSubstring_x27(v___x_3455_);
return v___x_3456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89));
v___x_3472_ = l_String_toRawSubstring_x27(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114));
v___x_3540_ = l_String_toRawSubstring_x27(v___x_3539_);
return v___x_3540_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117));
v___x_3545_ = l_String_toRawSubstring_x27(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122));
v___x_3555_ = l_String_toRawSubstring_x27(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128));
v___x_3569_ = l_String_toRawSubstring_x27(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131));
v___x_3574_ = l_String_toRawSubstring_x27(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139));
v___x_3596_ = l_String_toRawSubstring_x27(v___x_3595_);
return v___x_3596_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150));
v___x_3625_ = l_String_toRawSubstring_x27(v___x_3624_);
return v___x_3625_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168));
v___x_3666_ = l_String_toRawSubstring_x27(v___x_3665_);
return v___x_3666_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176(void){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175));
v___x_3682_ = l_String_toRawSubstring_x27(v___x_3681_);
return v___x_3682_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190));
v___x_3705_ = l_String_toRawSubstring_x27(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198));
v___x_3724_ = l_String_toRawSubstring_x27(v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17));
v___x_3728_ = l_String_toRawSubstring_x27(v___x_3727_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209));
v___x_3751_ = l_String_toRawSubstring_x27(v___x_3750_);
return v___x_3751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212));
v___x_3756_ = l_String_toRawSubstring_x27(v___x_3755_);
return v___x_3756_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221(void){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220));
v___x_3777_ = l_String_toRawSubstring_x27(v___x_3776_);
return v___x_3777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224));
v___x_3784_ = l_String_toRawSubstring_x27(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232));
v___x_3799_ = l_String_toRawSubstring_x27(v___x_3798_);
return v___x_3799_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238));
v___x_3811_ = l_String_toRawSubstring_x27(v___x_3810_);
return v___x_3811_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243(void){
_start:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242));
v___x_3817_ = l_String_toRawSubstring_x27(v___x_3816_);
return v___x_3817_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246));
v___x_3823_ = l_String_toRawSubstring_x27(v___x_3822_);
return v___x_3823_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253));
v___x_3838_ = l_String_toRawSubstring_x27(v___x_3837_);
return v___x_3838_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15));
v___x_3844_ = l_String_toRawSubstring_x27(v___x_3843_);
return v___x_3844_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261));
v___x_3855_ = l_String_toRawSubstring_x27(v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(lean_object* v_doc_x3f_3870_, lean_object* v_elabName_3871_, lean_object* v_type_3872_, lean_object* v_monadName_3873_, lean_object* v_adapt_3874_, lean_object* v_recover_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_quotContext_3878_; lean_object* v_currMacroScope_3879_; lean_object* v_ref_3880_; lean_object* v_ref_3881_; uint8_t v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___y_4018_; 
v_quotContext_3878_ = lean_ctor_get(v_a_3876_, 1);
v_currMacroScope_3879_ = lean_ctor_get(v_a_3876_, 2);
v_ref_3880_ = lean_ctor_get(v_a_3876_, 5);
v_ref_3881_ = l_Lean_replaceRef(v_type_3872_, v_ref_3880_);
v___x_3882_ = 0;
v___x_3883_ = l_Lean_SourceInfo_fromRef(v_ref_3881_, v___x_3882_);
lean_dec(v_ref_3881_);
v___x_3884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_3885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_3883_, 7);
v___x_3886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3883_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_3888_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_3889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3883_);
lean_ctor_set(v___x_3889_, 1, v___x_3887_);
lean_ctor_set(v___x_3889_, 2, v___x_3888_);
v___x_3890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
lean_inc_ref_n(v___x_3889_, 2);
v___x_3891_ = l_Lean_Syntax_node1(v___x_3883_, v___x_3890_, v___x_3889_);
v___x_3892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_3893_ = l_Lean_Syntax_node1(v___x_3883_, v___x_3892_, v___x_3889_);
v___x_3894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_3895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3883_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
lean_inc_n(v_type_3872_, 3);
v___x_3896_ = l_Lean_Syntax_node2(v___x_3883_, v___x_3887_, v___x_3895_, v_type_3872_);
v___x_3897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_3898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3883_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = l_Lean_Syntax_node6(v___x_3883_, v___x_3884_, v___x_3886_, v___x_3889_, v___x_3891_, v___x_3893_, v___x_3896_, v___x_3898_);
v___x_3900_ = l_Lean_SourceInfo_fromRef(v_ref_3880_, v___x_3882_);
v___x_3901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1));
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3));
lean_inc_n(v___x_3900_, 55);
v___x_3903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3900_);
lean_ctor_set(v___x_3903_, 1, v___x_3887_);
lean_ctor_set(v___x_3903_, 2, v___x_3888_);
v___x_3904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5));
v___x_3906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3900_);
lean_ctor_set(v___x_3906_, 1, v___x_3904_);
v___x_3907_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3905_, v___x_3906_);
v___x_3908_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3907_);
lean_inc_ref_n(v___x_3903_, 21);
v___x_3909_ = l_Lean_Syntax_node7(v___x_3900_, v___x_3902_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3908_, v___x_3903_);
v___x_3910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7));
v___x_3911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8));
v___x_3912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3900_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10));
v___x_3914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12);
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13));
lean_inc_n(v_currMacroScope_3879_, 9);
lean_inc_n(v_quotContext_3878_, 9);
v___x_3916_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3915_, v_currMacroScope_3879_);
v___x_3917_ = lean_box(0);
v___x_3918_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3900_);
lean_ctor_set(v___x_3918_, 1, v___x_3914_);
lean_ctor_set(v___x_3918_, 2, v___x_3916_);
lean_ctor_set(v___x_3918_, 3, v___x_3917_);
lean_inc_ref(v___x_3918_);
v___x_3919_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3913_, v___x_3918_, v___x_3903_);
v___x_3920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15));
v___x_3921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17));
v___x_3922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
v___x_3923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3900_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19);
v___x_3925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20));
v___x_3926_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3925_, v_currMacroScope_3879_);
v___x_3927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3900_);
lean_ctor_set(v___x_3927_, 1, v___x_3924_);
lean_ctor_set(v___x_3927_, 2, v___x_3926_);
lean_ctor_set(v___x_3927_, 3, v___x_3917_);
lean_inc_ref(v___x_3927_);
v___x_3928_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3900_);
lean_ctor_set(v___x_3929_, 1, v___x_3894_);
v___x_3930_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22);
v___x_3931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23));
v___x_3932_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3931_, v_currMacroScope_3879_);
v___x_3933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28));
v___x_3934_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3900_);
lean_ctor_set(v___x_3934_, 1, v___x_3930_);
lean_ctor_set(v___x_3934_, 2, v___x_3932_);
lean_ctor_set(v___x_3934_, 3, v___x_3933_);
lean_inc_ref_n(v___x_3929_, 2);
v___x_3935_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_3929_, v___x_3934_);
v___x_3936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_3937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3900_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
lean_inc_ref_n(v___x_3937_, 2);
lean_inc_ref_n(v___x_3923_, 2);
v___x_3938_ = l_Lean_Syntax_node5(v___x_3900_, v___x_3921_, v___x_3923_, v___x_3928_, v___x_3935_, v___x_3903_, v___x_3937_);
v___x_3939_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3938_);
v___x_3940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30));
v___x_3941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_3942_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32);
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33));
v___x_3944_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3943_, v_currMacroScope_3879_);
v___x_3945_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36));
v___x_3946_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3900_);
lean_ctor_set(v___x_3946_, 1, v___x_3942_);
lean_ctor_set(v___x_3946_, 2, v___x_3944_);
lean_ctor_set(v___x_3946_, 3, v___x_3945_);
v___x_3947_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v_type_3872_);
lean_inc(v___x_3947_);
v___x_3948_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_3946_, v___x_3947_);
v___x_3949_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3940_, v___x_3929_, v___x_3948_);
lean_inc(v___x_3949_);
v___x_3950_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3949_);
lean_inc(v___x_3950_);
lean_inc(v___x_3939_);
v___x_3951_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3920_, v___x_3939_, v___x_3950_);
v___x_3952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38));
v___x_3953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_3954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3900_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42));
v___x_3957_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3956_, v_currMacroScope_3879_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45));
v___x_3959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3900_);
lean_ctor_set(v___x_3959_, 1, v___x_3955_);
lean_ctor_set(v___x_3959_, 2, v___x_3957_);
lean_ctor_set(v___x_3959_, 3, v___x_3958_);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47));
v___x_3961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49);
v___x_3962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50));
v___x_3963_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3962_, v_currMacroScope_3879_);
v___x_3964_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3900_);
lean_ctor_set(v___x_3964_, 1, v___x_3961_);
lean_ctor_set(v___x_3964_, 2, v___x_3963_);
lean_ctor_set(v___x_3964_, 3, v___x_3917_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52));
v___x_3966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_3967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3900_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54);
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55));
v___x_3970_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3969_, v_currMacroScope_3879_);
v___x_3971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3900_);
lean_ctor_set(v___x_3971_, 1, v___x_3968_);
lean_ctor_set(v___x_3971_, 2, v___x_3970_);
lean_ctor_set(v___x_3971_, 3, v___x_3917_);
lean_inc_ref(v___x_3967_);
v___x_3972_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3965_, v___x_3967_, v___x_3971_);
lean_inc_ref_n(v___x_3954_, 2);
v___x_3973_ = l_Lean_Syntax_node5(v___x_3900_, v___x_3960_, v___x_3923_, v___x_3964_, v___x_3954_, v___x_3972_, v___x_3937_);
v___x_3974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57));
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_3976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3900_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
lean_inc_ref(v___x_3976_);
v___x_3977_ = l_Lean_Syntax_node3(v___x_3900_, v___x_3974_, v___x_3976_, v___x_3976_, v_type_3872_);
lean_inc(v___x_3977_);
v___x_3978_ = l_Lean_Syntax_node4(v___x_3900_, v___x_3887_, v___x_3973_, v_type_3872_, v___x_3977_, v___x_3927_);
v___x_3979_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_3959_, v___x_3978_);
v___x_3980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60));
v___x_3981_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3980_, v___x_3903_, v___x_3903_);
lean_inc(v___x_3981_);
v___x_3982_ = l_Lean_Syntax_node4(v___x_3900_, v___x_3952_, v___x_3954_, v___x_3979_, v___x_3981_, v___x_3903_);
lean_inc_ref(v___x_3912_);
v___x_3983_ = l_Lean_Syntax_node5(v___x_3900_, v___x_3910_, v___x_3912_, v___x_3919_, v___x_3951_, v___x_3982_, v___x_3903_);
v___x_3984_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3901_, v___x_3909_, v___x_3983_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62));
v___x_3986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63));
v___x_3987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3900_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65));
v___x_3989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67));
v___x_3990_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3989_, v___x_3903_);
v___x_3991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70));
v___x_3992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72);
v___x_3993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73));
v___x_3994_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3993_, v_currMacroScope_3879_);
v___x_3995_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3900_);
lean_ctor_set(v___x_3995_, 1, v___x_3992_);
lean_ctor_set(v___x_3995_, 2, v___x_3994_);
lean_ctor_set(v___x_3995_, 3, v___x_3917_);
v___x_3996_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3918_);
v___x_3997_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3991_, v___x_3995_, v___x_3996_);
v___x_3998_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3988_, v___x_3990_, v___x_3997_);
v___x_3999_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74));
v___x_4001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3900_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l_Lean_Syntax_node3(v___x_3900_, v___x_3985_, v___x_3987_, v___x_3999_, v___x_4001_);
v___x_4003_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4002_);
v___x_4004_ = l_Lean_Syntax_node7(v___x_3900_, v___x_3902_, v___x_3903_, v___x_4003_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_);
v___x_4005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75));
v___x_4006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76));
v___x_4007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_3900_);
lean_ctor_set(v___x_4007_, 1, v___x_4005_);
v___x_4008_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78);
v___x_4009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79));
v___x_4010_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4009_, v_currMacroScope_3879_);
v___x_4011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4011_, 0, v___x_3900_);
lean_ctor_set(v___x_4011_, 1, v___x_4008_);
lean_ctor_set(v___x_4011_, 2, v___x_4010_);
lean_ctor_set(v___x_4011_, 3, v___x_3917_);
lean_inc_ref(v___x_4011_);
v___x_4012_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3913_, v___x_4011_, v___x_3903_);
v___x_4013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81));
v___x_4014_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4013_, v___x_3939_, v___x_3949_);
v___x_4015_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4006_, v___x_4007_, v___x_4012_, v___x_4014_, v___x_3903_);
v___x_4016_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3901_, v___x_4004_, v___x_4015_);
if (lean_obj_tag(v_doc_x3f_3870_) == 1)
{
lean_object* v_val_4348_; lean_object* v___x_4349_; 
v_val_4348_ = lean_ctor_get(v_doc_x3f_3870_, 0);
lean_inc(v_val_4348_);
lean_dec_ref_known(v_doc_x3f_3870_, 1);
v___x_4349_ = l_Array_mkArray1___redArg(v_val_4348_);
v___y_4018_ = v___x_4349_;
goto v___jp_4017_;
}
else
{
lean_object* v___x_4350_; 
lean_dec(v_doc_x3f_3870_);
v___x_4350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268));
v___y_4018_ = v___x_4350_;
goto v___jp_4017_;
}
v___jp_4017_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4019_ = l_Array_append___redArg(v___x_3888_, v___y_4018_);
lean_dec_ref(v___y_4018_);
lean_inc_n(v___x_3900_, 183);
v___x_4020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4020_, 0, v___x_3900_);
lean_ctor_set(v___x_4020_, 1, v___x_3887_);
lean_ctor_set(v___x_4020_, 2, v___x_4019_);
lean_inc_ref_n(v___x_3903_, 57);
v___x_4021_ = l_Lean_Syntax_node7(v___x_3900_, v___x_3902_, v___x_4020_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_, v___x_3903_);
v___x_4022_ = lean_box(2);
v___x_4023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82));
v___x_4024_ = lean_unsigned_to_nat(2u);
v___x_4025_ = lean_mk_empty_array_with_capacity(v___x_4024_);
v___x_4026_ = lean_array_push(v___x_4025_, v_elabName_3871_);
v___x_4027_ = lean_array_push(v___x_4026_, v___x_4023_);
v___x_4028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4022_);
lean_ctor_set(v___x_4028_, 1, v___x_3913_);
lean_ctor_set(v___x_4028_, 2, v___x_4027_);
v___x_4029_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84);
v___x_4030_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85));
lean_inc_n(v_currMacroScope_3879_, 26);
lean_inc_n(v_quotContext_3878_, 26);
v___x_4031_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4030_, v_currMacroScope_3879_);
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88));
v___x_4033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4033_, 0, v___x_3900_);
lean_ctor_set(v___x_4033_, 1, v___x_4029_);
lean_ctor_set(v___x_4033_, 2, v___x_4031_);
lean_ctor_set(v___x_4033_, 3, v___x_4032_);
lean_inc_ref(v___x_4033_);
v___x_4034_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4033_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90);
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91));
v___x_4037_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4036_, v_currMacroScope_3879_);
v___x_4038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96));
v___x_4039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4039_, 0, v___x_3900_);
lean_ctor_set(v___x_4039_, 1, v___x_4035_);
lean_ctor_set(v___x_4039_, 2, v___x_4037_);
lean_ctor_set(v___x_4039_, 3, v___x_4038_);
lean_inc_ref(v___x_3929_);
v___x_4040_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_3929_, v___x_4039_);
lean_inc_ref_n(v___x_3937_, 3);
lean_inc(v___x_4034_);
lean_inc_ref_n(v___x_3923_, 2);
v___x_4041_ = l_Lean_Syntax_node5(v___x_3900_, v___x_3921_, v___x_3923_, v___x_4034_, v___x_4040_, v___x_3903_, v___x_3937_);
v___x_4042_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4041_);
v___x_4043_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v_monadName_3873_, v___x_3947_);
v___x_4044_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3940_, v___x_3929_, v___x_4043_);
v___x_4045_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4044_);
v___x_4046_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3920_, v___x_4042_, v___x_4045_);
v___x_4047_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97));
v___x_4048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98));
v___x_4049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_3900_);
lean_ctor_set(v___x_4049_, 1, v___x_4047_);
v___x_4050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100));
v___x_4051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102));
v___x_4052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104));
v___x_4053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105));
v___x_4054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_3900_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107));
v___x_4056_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4055_, v___x_3903_);
v___x_4057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109));
v___x_4058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111));
v___x_4059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113));
v___x_4060_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4062_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4061_, v_currMacroScope_3879_);
v___x_4063_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4063_, 0, v___x_3900_);
lean_ctor_set(v___x_4063_, 1, v___x_4060_);
lean_ctor_set(v___x_4063_, 2, v___x_4062_);
lean_ctor_set(v___x_4063_, 3, v___x_3917_);
lean_inc_ref(v___x_4063_);
v___x_4064_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4059_, v___x_4063_);
lean_inc_ref_n(v___x_3954_, 5);
v___x_4065_ = l_Lean_Syntax_node5(v___x_3900_, v___x_4058_, v___x_4064_, v___x_3903_, v___x_3903_, v___x_3954_, v_recover_3875_);
v___x_4066_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4057_, v___x_4065_);
lean_inc_n(v___x_4056_, 5);
lean_inc_ref_n(v___x_4054_, 5);
v___x_4067_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4052_, v___x_4054_, v___x_3903_, v___x_4056_, v___x_4066_);
v___x_4068_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4067_, v___x_3903_);
v___x_4069_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118);
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119));
v___x_4071_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4070_, v_currMacroScope_3879_);
v___x_4072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121));
v___x_4073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4073_, 0, v___x_3900_);
lean_ctor_set(v___x_4073_, 1, v___x_4069_);
lean_ctor_set(v___x_4073_, 2, v___x_4071_);
lean_ctor_set(v___x_4073_, 3, v___x_4072_);
lean_inc_ref(v___x_4073_);
v___x_4074_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4059_, v___x_4073_);
v___x_4075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123);
v___x_4076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124));
v___x_4077_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4076_, v_currMacroScope_3879_);
v___x_4078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127));
v___x_4079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4079_, 0, v___x_3900_);
lean_ctor_set(v___x_4079_, 1, v___x_4075_);
lean_ctor_set(v___x_4079_, 2, v___x_4077_);
lean_ctor_set(v___x_4079_, 3, v___x_4078_);
v___x_4080_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129);
v___x_4081_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130));
v___x_4082_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4081_, v_currMacroScope_3879_);
v___x_4083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4083_, 0, v___x_3900_);
lean_ctor_set(v___x_4083_, 1, v___x_4080_);
lean_ctor_set(v___x_4083_, 2, v___x_4082_);
lean_ctor_set(v___x_4083_, 3, v___x_3917_);
lean_inc_ref(v___x_4083_);
v___x_4084_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4059_, v___x_4083_);
v___x_4085_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132);
v___x_4086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133));
v___x_4087_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4086_, v_currMacroScope_3879_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136));
v___x_4089_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4089_, 0, v___x_3900_);
lean_ctor_set(v___x_4089_, 1, v___x_4085_);
lean_ctor_set(v___x_4089_, 2, v___x_4087_);
lean_ctor_set(v___x_4089_, 3, v___x_4088_);
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4093_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4094_ = lean_box(0);
v___x_4095_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4094_, v_currMacroScope_3879_);
v___x_4096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4097_, 0, v___x_3900_);
lean_ctor_set(v___x_4097_, 1, v___x_4093_);
lean_ctor_set(v___x_4097_, 2, v___x_4095_);
lean_ctor_set(v___x_4097_, 3, v___x_4096_);
v___x_4098_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4092_, v___x_4097_);
v___x_4099_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4091_, v___x_3923_, v___x_4098_);
v___x_4100_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141));
v___x_4102_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4101_, v_currMacroScope_3879_);
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144));
v___x_4104_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4104_, 0, v___x_3900_);
lean_ctor_set(v___x_4104_, 1, v___x_4100_);
lean_ctor_set(v___x_4104_, 2, v___x_4102_);
lean_ctor_set(v___x_4104_, 3, v___x_4103_);
v___x_4105_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4104_, v___x_4034_);
lean_inc(v___x_4099_);
v___x_4106_ = l_Lean_Syntax_node3(v___x_3900_, v___x_4090_, v___x_4099_, v___x_4105_, v___x_3937_);
v___x_4107_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4106_);
v___x_4108_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4089_, v___x_4107_);
v___x_4109_ = l_Lean_Syntax_node5(v___x_3900_, v___x_4058_, v___x_4084_, v___x_3903_, v___x_3903_, v___x_3954_, v___x_4108_);
v___x_4110_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4057_, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4052_, v___x_4054_, v___x_3903_, v___x_4056_, v___x_4110_);
v___x_4112_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4111_, v___x_3903_);
v___x_4113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146));
v___x_4114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147));
v___x_4115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_3900_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149));
v___x_4117_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151);
v___x_4118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153));
v___x_4119_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4118_, v_currMacroScope_3879_);
v___x_4120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4120_, 0, v___x_3900_);
lean_ctor_set(v___x_4120_, 1, v___x_4117_);
lean_ctor_set(v___x_4120_, 2, v___x_4119_);
lean_ctor_set(v___x_4120_, 3, v___x_3917_);
v___x_4121_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4116_, v___x_3903_, v___x_4120_);
v___x_4122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154));
v___x_4123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_3900_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156));
v___x_4125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157));
v___x_4126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_3900_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3899_);
lean_inc_ref(v___x_4126_);
v___x_4128_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4124_, v___x_4126_, v___x_4127_);
v___x_4129_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4128_, v___x_3903_);
lean_inc(v___x_4129_);
v___x_4130_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4129_);
v___x_4131_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4130_);
lean_inc(v___x_4131_);
lean_inc_ref_n(v___x_4123_, 3);
lean_inc_ref_n(v___x_4115_, 3);
v___x_4132_ = l_Lean_Syntax_node6(v___x_3900_, v___x_4113_, v___x_4115_, v___x_4121_, v___x_4123_, v___x_4131_, v___x_3903_, v___x_3903_);
v___x_4133_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4132_, v___x_3903_);
v___x_4134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159));
v___x_4135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160));
v___x_4136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_3900_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_3900_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4142_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169);
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170));
v___x_4144_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4143_, v_currMacroScope_3879_);
v___x_4145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174));
v___x_4146_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4146_, 0, v___x_3900_);
lean_ctor_set(v___x_4146_, 1, v___x_4142_);
lean_ctor_set(v___x_4146_, 2, v___x_4144_);
lean_ctor_set(v___x_4146_, 3, v___x_4145_);
v___x_4147_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4146_);
lean_inc_ref_n(v___x_4140_, 2);
v___x_4148_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4138_, v___x_4140_, v___x_4147_);
v___x_4149_ = l_Lean_Syntax_node3(v___x_3900_, v___x_4090_, v___x_4099_, v___x_4148_, v___x_3937_);
v___x_4150_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176);
v___x_4151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177));
v___x_4152_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4151_, v_currMacroScope_3879_);
v___x_4153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4153_, 0, v___x_3900_);
lean_ctor_set(v___x_4153_, 1, v___x_4150_);
lean_ctor_set(v___x_4153_, 2, v___x_4152_);
lean_ctor_set(v___x_4153_, 3, v___x_3917_);
v___x_4154_ = l_Lean_Syntax_node3(v___x_3900_, v___x_4137_, v___x_4149_, v___x_3967_, v___x_4153_);
lean_inc_n(v___x_3977_, 3);
v___x_4155_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_3977_);
v___x_4156_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4154_, v___x_4155_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179));
v___x_4158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180));
v___x_4159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_3900_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182));
v___x_4161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183));
v___x_4162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_3900_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185));
v___x_4164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187));
v___x_4165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188));
v___x_4166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_3900_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4164_, v___x_4166_);
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189));
v___x_4169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_3900_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4164_, v___x_4169_);
lean_inc(v___x_4170_);
v___x_4171_ = l_Lean_Syntax_node3(v___x_3900_, v___x_4163_, v___x_4167_, v___x_3977_, v___x_4170_);
lean_inc_ref_n(v___x_4162_, 2);
v___x_4172_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4160_, v___x_4162_, v___x_4171_);
lean_inc_ref_n(v___x_4159_, 2);
v___x_4173_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4157_, v___x_4159_, v___x_4172_);
v___x_4174_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4173_);
v___x_4175_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4174_, v___x_3903_);
v___x_4176_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4175_);
v___x_4177_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4176_);
lean_inc_ref_n(v___x_4049_, 2);
v___x_4178_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4134_, v___x_4136_, v___x_4156_, v___x_4049_, v___x_4177_);
v___x_4179_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4178_, v___x_3903_);
v___x_4180_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191);
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192));
v___x_4182_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4181_, v_currMacroScope_3879_);
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197));
v___x_4184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4184_, 0, v___x_3900_);
lean_ctor_set(v___x_4184_, 1, v___x_4180_);
lean_ctor_set(v___x_4184_, 2, v___x_4182_);
lean_ctor_set(v___x_4184_, 3, v___x_4183_);
v___x_4185_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199);
v___x_4186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200));
v___x_4187_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4186_, v_currMacroScope_3879_);
v___x_4188_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4188_, 0, v___x_3900_);
lean_ctor_set(v___x_4188_, 1, v___x_4185_);
lean_ctor_set(v___x_4188_, 2, v___x_4187_);
lean_ctor_set(v___x_4188_, 3, v___x_3917_);
v___x_4189_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201);
v___x_4190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202));
v___x_4191_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4190_, v_currMacroScope_3879_);
v___x_4192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204));
v___x_4193_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4193_, 0, v___x_3900_);
lean_ctor_set(v___x_4193_, 1, v___x_4189_);
lean_ctor_set(v___x_4193_, 2, v___x_4191_);
lean_ctor_set(v___x_4193_, 3, v___x_4192_);
v___x_4194_ = l_Lean_Syntax_node5(v___x_3900_, v___x_3960_, v___x_3923_, v___x_4188_, v___x_3954_, v___x_4193_, v___x_3937_);
v___x_4195_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_4194_, v___x_3977_);
v___x_4196_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4184_, v___x_4195_);
v___x_4197_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4196_);
v___x_4198_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4197_, v___x_3903_);
v___x_4199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206));
v___x_4200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208));
v___x_4201_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210);
v___x_4202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211));
v___x_4203_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4202_, v_currMacroScope_3879_);
v___x_4204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4204_, 0, v___x_3900_);
lean_ctor_set(v___x_4204_, 1, v___x_4201_);
lean_ctor_set(v___x_4204_, 2, v___x_4203_);
lean_ctor_set(v___x_4204_, 3, v___x_3917_);
v___x_4205_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213);
v___x_4206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214));
v___x_4207_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4206_, v_currMacroScope_3879_);
v___x_4208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219));
v___x_4209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4209_, 0, v___x_3900_);
lean_ctor_set(v___x_4209_, 1, v___x_4205_);
lean_ctor_set(v___x_4209_, 2, v___x_4207_);
lean_ctor_set(v___x_4209_, 3, v___x_4208_);
v___x_4210_ = l_Lean_Syntax_node3(v___x_3900_, v___x_3887_, v___x_4063_, v___x_3977_, v___x_4083_);
v___x_4211_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4209_, v___x_4210_);
v___x_4212_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4211_);
lean_inc_ref(v___x_4204_);
v___x_4213_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4200_, v___x_4204_, v___x_3903_, v___x_4140_, v___x_4212_);
v___x_4214_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4199_, v___x_4054_, v___x_3903_, v___x_4056_, v___x_4213_);
v___x_4215_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4214_, v___x_3903_);
v___x_4216_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221);
v___x_4217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223));
v___x_4218_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4217_, v_currMacroScope_3879_);
v___x_4219_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4219_, 0, v___x_3900_);
lean_ctor_set(v___x_4219_, 1, v___x_4216_);
lean_ctor_set(v___x_4219_, 2, v___x_4218_);
lean_ctor_set(v___x_4219_, 3, v___x_3917_);
v___x_4220_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4116_, v___x_3903_, v___x_4219_);
v___x_4221_ = l_Lean_Syntax_node6(v___x_3900_, v___x_4113_, v___x_4115_, v___x_4220_, v___x_4123_, v___x_4131_, v___x_3903_, v___x_3903_);
v___x_4222_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4221_, v___x_3903_);
v___x_4223_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225);
v___x_4224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227));
v___x_4225_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4224_, v_currMacroScope_3879_);
v___x_4226_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4226_, 0, v___x_3900_);
lean_ctor_set(v___x_4226_, 1, v___x_4223_);
lean_ctor_set(v___x_4226_, 2, v___x_4225_);
lean_ctor_set(v___x_4226_, 3, v___x_3917_);
v___x_4227_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4116_, v___x_3903_, v___x_4226_);
v___x_4228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228));
v___x_4229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_3900_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v___x_4230_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4164_, v___x_4229_);
v___x_4231_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4163_, v___x_4230_);
v___x_4232_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4160_, v___x_4162_, v___x_4231_);
v___x_4233_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4157_, v___x_4159_, v___x_4232_);
v___x_4234_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4233_);
v___x_4235_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4234_, v___x_3903_);
v___x_4236_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4235_);
v___x_4237_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4236_);
v___x_4238_ = l_Lean_Syntax_node6(v___x_3900_, v___x_4113_, v___x_4115_, v___x_4227_, v___x_4123_, v___x_4237_, v___x_3903_, v___x_3903_);
v___x_4239_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4238_, v___x_3903_);
v___x_4240_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230));
v___x_4241_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231));
v___x_4242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_3900_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233);
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234));
v___x_4245_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4244_, v_currMacroScope_3879_);
v___x_4246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4246_, 0, v___x_3900_);
lean_ctor_set(v___x_4246_, 1, v___x_4243_);
lean_ctor_set(v___x_4246_, 2, v___x_4245_);
lean_ctor_set(v___x_4246_, 3, v___x_3917_);
v___x_4247_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4204_);
lean_inc(v___x_4247_);
v___x_4248_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4011_, v___x_4247_);
v___x_4249_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4248_);
lean_inc_ref(v___x_4246_);
v___x_4250_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4200_, v___x_4246_, v___x_3903_, v___x_4140_, v___x_4249_);
v___x_4251_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4199_, v___x_4054_, v___x_3903_, v___x_4056_, v___x_4250_);
v___x_4252_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4251_, v___x_3903_);
v___x_4253_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4246_);
v___x_4254_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4124_, v___x_4126_, v___x_4253_);
v___x_4255_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4254_, v___x_3903_);
v___x_4256_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_4252_, v___x_4255_);
v___x_4257_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4256_);
v___x_4258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236));
v___x_4259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237));
v___x_4260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_3900_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239);
v___x_4262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240));
v___x_4263_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4262_, v_currMacroScope_3879_);
v___x_4264_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4264_, 0, v___x_3900_);
lean_ctor_set(v___x_4264_, 1, v___x_4261_);
lean_ctor_set(v___x_4264_, 2, v___x_4263_);
lean_ctor_set(v___x_4264_, 3, v___x_3917_);
v___x_4265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241));
v___x_4266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_3900_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243);
v___x_4268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244));
v___x_4269_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4268_, v_currMacroScope_3879_);
v___x_4270_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4270_, 0, v___x_3900_);
lean_ctor_set(v___x_4270_, 1, v___x_4267_);
lean_ctor_set(v___x_4270_, 2, v___x_4269_);
lean_ctor_set(v___x_4270_, 3, v___x_3917_);
lean_inc_ref_n(v___x_4270_, 2);
v___x_4271_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4059_, v___x_4270_);
v___x_4272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245));
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_3900_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4164_, v___x_4273_);
v___x_4275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247);
v___x_4276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248));
v___x_4277_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4276_, v_currMacroScope_3879_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251));
v___x_4279_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4279_, 0, v___x_3900_);
lean_ctor_set(v___x_4279_, 1, v___x_4275_);
lean_ctor_set(v___x_4279_, 2, v___x_4277_);
lean_ctor_set(v___x_4279_, 3, v___x_4278_);
v___x_4280_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4279_, v___x_4247_);
v___x_4281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252));
v___x_4282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_3900_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4164_, v___x_4282_);
v___x_4284_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254);
v___x_4285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256));
v___x_4286_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4285_, v_currMacroScope_3879_);
v___x_4287_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4287_, 0, v___x_3900_);
lean_ctor_set(v___x_4287_, 1, v___x_4284_);
lean_ctor_set(v___x_4287_, 2, v___x_4286_);
lean_ctor_set(v___x_4287_, 3, v___x_3917_);
v___x_4288_ = l_Lean_Syntax_node5(v___x_3900_, v___x_4163_, v___x_4274_, v___x_4280_, v___x_4283_, v___x_4287_, v___x_4170_);
v___x_4289_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4160_, v___x_4162_, v___x_4288_);
v___x_4290_ = l_Lean_Syntax_node5(v___x_3900_, v___x_4058_, v___x_4271_, v___x_3903_, v___x_3903_, v___x_3954_, v___x_4289_);
v___x_4291_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4057_, v___x_4290_);
v___x_4292_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4052_, v___x_4054_, v___x_3903_, v___x_4056_, v___x_4291_);
v___x_4293_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4292_, v___x_3903_);
v___x_4294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257);
v___x_4295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258));
v___x_4296_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4295_, v_currMacroScope_3879_);
v___x_4297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260));
v___x_4298_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4298_, 0, v___x_3900_);
lean_ctor_set(v___x_4298_, 1, v___x_4294_);
lean_ctor_set(v___x_4298_, 2, v___x_4296_);
lean_ctor_set(v___x_4298_, 3, v___x_4297_);
v___x_4299_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4116_, v___x_3903_, v___x_4298_);
v___x_4300_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262);
v___x_4301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263));
v___x_4302_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_4301_, v_currMacroScope_3879_);
v___x_4303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266));
v___x_4304_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4304_, 0, v___x_3900_);
lean_ctor_set(v___x_4304_, 1, v___x_4300_);
lean_ctor_set(v___x_4304_, 2, v___x_4302_);
lean_ctor_set(v___x_4304_, 3, v___x_4303_);
v___x_4305_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4270_);
v___x_4306_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4304_, v___x_4305_);
v___x_4307_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4306_);
v___x_4308_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4307_, v___x_3903_);
v___x_4309_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_4308_, v___x_4129_);
v___x_4310_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4309_);
v___x_4311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267));
v___x_4312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_3900_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4157_, v___x_4159_, v___x_4270_);
v___x_4314_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4314_, v___x_3903_);
v___x_4316_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4315_);
v___x_4317_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4316_);
v___x_4318_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_4312_, v___x_4317_);
v___x_4319_ = l_Lean_Syntax_node6(v___x_3900_, v___x_4113_, v___x_4115_, v___x_4299_, v___x_4123_, v___x_4310_, v___x_3903_, v___x_4318_);
v___x_4320_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4319_, v___x_3903_);
v___x_4321_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_4293_, v___x_4320_);
v___x_4322_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4321_);
v___x_4323_ = l_Lean_Syntax_node5(v___x_3900_, v___x_4258_, v___x_4260_, v___x_4264_, v___x_3903_, v___x_4266_, v___x_4322_);
v___x_4324_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4323_);
v___x_4325_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4240_, v___x_4242_, v___x_4257_, v___x_4324_, v___x_3903_);
v___x_4326_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4325_, v___x_3903_);
v___x_4327_ = l_Lean_Syntax_node8(v___x_3900_, v___x_3887_, v___x_4112_, v___x_4133_, v___x_4179_, v___x_4198_, v___x_4215_, v___x_4222_, v___x_4239_, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4327_);
v___x_4329_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4048_, v___x_4049_, v___x_4328_);
v___x_4330_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3887_, v___x_4033_, v___x_4329_);
v___x_4331_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v___x_4079_, v___x_4330_);
v___x_4332_ = l_Lean_Syntax_node5(v___x_3900_, v___x_4058_, v___x_4074_, v___x_3903_, v___x_3950_, v___x_3954_, v___x_4331_);
v___x_4333_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4057_, v___x_4332_);
v___x_4334_ = l_Lean_Syntax_node4(v___x_3900_, v___x_4052_, v___x_4054_, v___x_3903_, v___x_4056_, v___x_4333_);
v___x_4335_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4334_, v___x_3903_);
v___x_4336_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4141_, v___x_4073_);
v___x_4337_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4051_, v___x_4336_, v___x_3903_);
v___x_4338_ = l_Lean_Syntax_node3(v___x_3900_, v___x_3887_, v___x_4068_, v___x_4335_, v___x_4337_);
v___x_4339_ = l_Lean_Syntax_node1(v___x_3900_, v___x_4050_, v___x_4338_);
v___x_4340_ = l_Lean_Syntax_node2(v___x_3900_, v___x_4048_, v___x_4049_, v___x_4339_);
v___x_4341_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3887_, v___x_4340_);
v___x_4342_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3941_, v_adapt_3874_, v___x_4341_);
v___x_4343_ = l_Lean_Syntax_node4(v___x_3900_, v___x_3952_, v___x_3954_, v___x_4342_, v___x_3981_, v___x_3903_);
v___x_4344_ = l_Lean_Syntax_node5(v___x_3900_, v___x_3910_, v___x_3912_, v___x_4028_, v___x_4046_, v___x_4343_, v___x_3903_);
v___x_4345_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3901_, v___x_4021_, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_node3(v___x_3900_, v___x_3887_, v___x_3984_, v___x_4016_, v___x_4345_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
lean_ctor_set(v___x_4347_, 1, v_a_3877_);
return v___x_4347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___boxed(lean_object* v_doc_x3f_4351_, lean_object* v_elabName_4352_, lean_object* v_type_4353_, lean_object* v_monadName_4354_, lean_object* v_adapt_4355_, lean_object* v_recover_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v_doc_x3f_4351_, v_elabName_4352_, v_type_4353_, v_monadName_4354_, v_adapt_4355_, v_recover_4356_, v_a_4357_, v_a_4358_);
lean_dec_ref(v_a_4357_);
return v_res_4359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1(void){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0));
v___x_4404_ = l_String_toRawSubstring_x27(v___x_4403_);
return v___x_4404_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9(void){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4423_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8));
v___x_4424_ = l_Lean_mkCIdent(v___x_4423_);
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11));
v___x_4429_ = l_Lean_mkCIdent(v___x_4428_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(lean_object* v_x_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
lean_inc(v_x_4430_);
v___x_4434_ = l_Lean_Syntax_isOfKind(v_x_4430_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_dec(v_x_4430_);
v___x_4435_ = lean_box(1);
v___x_4436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
lean_ctor_set(v___x_4436_, 1, v_a_4432_);
return v___x_4436_;
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v_elabName_4440_; lean_object* v___x_4441_; lean_object* v_type_4442_; lean_object* v___y_4444_; lean_object* v___x_4497_; 
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = l_Lean_Syntax_getArg(v_x_4430_, v___x_4437_);
v___x_4439_ = lean_unsigned_to_nat(2u);
v_elabName_4440_ = l_Lean_Syntax_getArg(v_x_4430_, v___x_4439_);
v___x_4441_ = lean_unsigned_to_nat(3u);
v_type_4442_ = l_Lean_Syntax_getArg(v_x_4430_, v___x_4441_);
lean_dec(v_x_4430_);
v___x_4497_ = l_Lean_Syntax_getOptional_x3f(v___x_4438_);
lean_dec(v___x_4438_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_box(0);
v___y_4444_ = v___x_4498_;
goto v___jp_4443_;
}
else
{
lean_object* v_val_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
v_val_4499_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4497_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_val_4499_);
lean_dec(v___x_4497_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_val_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
v___y_4444_ = v___x_4504_;
goto v___jp_4443_;
}
}
}
v___jp_4443_:
{
lean_object* v_quotContext_4445_; lean_object* v_currMacroScope_4446_; lean_object* v_ref_4447_; uint8_t v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v_a_4488_; lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
v_quotContext_4445_ = lean_ctor_get(v_a_4431_, 1);
v_currMacroScope_4446_ = lean_ctor_get(v_a_4431_, 2);
v_ref_4447_ = lean_ctor_get(v_a_4431_, 5);
v___x_4448_ = 0;
v___x_4449_ = l_Lean_SourceInfo_fromRef(v_ref_4447_, v___x_4448_);
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_4449_, 12);
v___x_4454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4449_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
v___x_4455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4457_ = lean_box(0);
lean_inc_n(v_currMacroScope_4446_, 3);
lean_inc_n(v_quotContext_4445_, 3);
v___x_4458_ = l_Lean_addMacroScope(v_quotContext_4445_, v___x_4457_, v_currMacroScope_4446_);
v___x_4459_ = lean_box(0);
v___x_4460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4461_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4449_);
lean_ctor_set(v___x_4461_, 1, v___x_4456_);
lean_ctor_set(v___x_4461_, 2, v___x_4458_);
lean_ctor_set(v___x_4461_, 3, v___x_4460_);
v___x_4462_ = l_Lean_Syntax_node1(v___x_4449_, v___x_4455_, v___x_4461_);
v___x_4463_ = l_Lean_Syntax_node2(v___x_4449_, v___x_4452_, v___x_4454_, v___x_4462_);
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4449_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4468_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1);
v___x_4469_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2));
v___x_4470_ = l_Lean_addMacroScope(v_quotContext_4445_, v___x_4469_, v_currMacroScope_4446_);
v___x_4471_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6));
v___x_4472_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4449_);
lean_ctor_set(v___x_4472_, 1, v___x_4468_);
lean_ctor_set(v___x_4472_, 2, v___x_4470_);
lean_ctor_set(v___x_4472_, 3, v___x_4471_);
v___x_4473_ = l_Lean_Syntax_node1(v___x_4449_, v___x_4467_, v___x_4472_);
v___x_4474_ = l_Lean_Syntax_node2(v___x_4449_, v___x_4464_, v___x_4466_, v___x_4473_);
v___x_4475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_4476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4449_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = l_Lean_Syntax_node3(v___x_4449_, v___x_4451_, v___x_4463_, v___x_4474_, v___x_4476_);
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_4479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4449_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
v___x_4480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4482_ = l_Lean_addMacroScope(v_quotContext_4445_, v___x_4481_, v_currMacroScope_4446_);
v___x_4483_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4449_);
lean_ctor_set(v___x_4483_, 1, v___x_4480_);
lean_ctor_set(v___x_4483_, 2, v___x_4482_);
lean_ctor_set(v___x_4483_, 3, v___x_4459_);
v___x_4484_ = l_Lean_Syntax_node3(v___x_4449_, v___x_4450_, v___x_4477_, v___x_4479_, v___x_4483_);
v___x_4485_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9);
v___x_4486_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12);
v___x_4487_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4444_, v_elabName_4440_, v_type_4442_, v___x_4485_, v___x_4486_, v___x_4484_, v_a_4431_, v_a_4432_);
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_a_4489_ = lean_ctor_get(v___x_4487_, 1);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4487_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4488_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___boxed(lean_object* v_x_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(v_x_4507_, v_a_4508_, v_a_4509_);
lean_dec_ref(v_a_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4517_ = lean_unsigned_to_nat(2u);
v___x_4518_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4516_, v___x_4517_, v_a_4512_, v_a_4513_, v_a_4514_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed(lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
return v_res_4523_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed), 4, 0);
v___x_4525_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4525_, 0, v___x_4524_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1(){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
v___x_4528_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0);
v___x_4529_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4527_, v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___boxed(lean_object* v_a_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
return v_res_4531_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1));
v___x_4565_ = l_Lean_mkCIdent(v___x_4564_);
return v___x_4565_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4));
v___x_4573_ = l_Lean_mkCIdent(v___x_4572_);
return v___x_4573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6(void){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18));
v___x_4575_ = l_Lean_mkCIdent(v___x_4574_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(lean_object* v_x_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_){
_start:
{
lean_object* v___x_4579_; uint8_t v___x_4580_; 
v___x_4579_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
lean_inc(v_x_4576_);
v___x_4580_ = l_Lean_Syntax_isOfKind(v_x_4576_, v___x_4579_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
lean_dec(v_x_4576_);
v___x_4581_ = lean_box(1);
v___x_4582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v_a_4578_);
return v___x_4582_;
}
else
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v_elabName_4586_; lean_object* v___x_4587_; lean_object* v_type_4588_; lean_object* v___y_4590_; lean_object* v___x_4604_; 
v___x_4583_ = lean_unsigned_to_nat(0u);
v___x_4584_ = l_Lean_Syntax_getArg(v_x_4576_, v___x_4583_);
v___x_4585_ = lean_unsigned_to_nat(2u);
v_elabName_4586_ = l_Lean_Syntax_getArg(v_x_4576_, v___x_4585_);
v___x_4587_ = lean_unsigned_to_nat(3u);
v_type_4588_ = l_Lean_Syntax_getArg(v_x_4576_, v___x_4587_);
lean_dec(v_x_4576_);
v___x_4604_ = l_Lean_Syntax_getOptional_x3f(v___x_4584_);
lean_dec(v___x_4584_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_box(0);
v___y_4590_ = v___x_4605_;
goto v___jp_4589_;
}
else
{
lean_object* v_val_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
v_val_4606_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4604_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_val_4606_);
lean_dec(v___x_4604_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_val_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
v___y_4590_ = v___x_4611_;
goto v___jp_4589_;
}
}
}
v___jp_4589_:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v_a_4595_; lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
v___x_4591_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2);
v___x_4592_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5);
v___x_4593_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6);
v___x_4594_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4590_, v_elabName_4586_, v_type_4588_, v___x_4591_, v___x_4592_, v___x_4593_, v_a_4577_, v_a_4578_);
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
v_a_4596_ = lean_ctor_get(v___x_4594_, 1);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4594_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_inc(v_a_4595_);
lean_dec(v___x_4594_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4595_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___boxed(lean_object* v_x_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(v_x_4614_, v_a_4615_, v_a_4616_);
lean_dec_ref(v_a_4615_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4623_ = lean_unsigned_to_nat(2u);
v___x_4624_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4622_, v___x_4623_, v_a_4618_, v_a_4619_, v_a_4620_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed(lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(v_a_4625_, v_a_4626_, v_a_4627_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
return v_res_4629_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed), 4, 0);
v___x_4631_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4631_, 0, v___x_4630_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
v___x_4634_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0);
v___x_4635_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4633_, v___x_4634_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___boxed(lean_object* v_a_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
return v_res_4637_;
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
