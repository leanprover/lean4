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
v_options_139_ = lean_ctor_get(v___y_131_, 1);
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
v_ref_156_ = lean_ctor_get(v___y_153_, 4);
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
lean_object* v_toCold_329_; lean_object* v_options_330_; lean_object* v_currRecDepth_331_; lean_object* v_maxRecDepth_332_; lean_object* v_ref_333_; lean_object* v_currNamespace_334_; lean_object* v_openDecls_335_; lean_object* v_initHeartbeats_336_; lean_object* v_maxHeartbeats_337_; lean_object* v_currMacroScope_338_; uint8_t v_diag_339_; uint8_t v_suppressElabErrors_340_; lean_object* v_ref_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_toCold_329_ = lean_ctor_get(v___y_326_, 0);
v_options_330_ = lean_ctor_get(v___y_326_, 1);
v_currRecDepth_331_ = lean_ctor_get(v___y_326_, 2);
v_maxRecDepth_332_ = lean_ctor_get(v___y_326_, 3);
v_ref_333_ = lean_ctor_get(v___y_326_, 4);
v_currNamespace_334_ = lean_ctor_get(v___y_326_, 5);
v_openDecls_335_ = lean_ctor_get(v___y_326_, 6);
v_initHeartbeats_336_ = lean_ctor_get(v___y_326_, 7);
v_maxHeartbeats_337_ = lean_ctor_get(v___y_326_, 8);
v_currMacroScope_338_ = lean_ctor_get(v___y_326_, 9);
v_diag_339_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*10);
v_suppressElabErrors_340_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*10 + 1);
v_ref_341_ = l_Lean_replaceRef(v_ref_322_, v_ref_333_);
lean_inc(v_currMacroScope_338_);
lean_inc(v_maxHeartbeats_337_);
lean_inc(v_initHeartbeats_336_);
lean_inc(v_openDecls_335_);
lean_inc(v_currNamespace_334_);
lean_inc(v_maxRecDepth_332_);
lean_inc(v_currRecDepth_331_);
lean_inc_ref(v_options_330_);
lean_inc_ref(v_toCold_329_);
v___x_342_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_342_, 0, v_toCold_329_);
lean_ctor_set(v___x_342_, 1, v_options_330_);
lean_ctor_set(v___x_342_, 2, v_currRecDepth_331_);
lean_ctor_set(v___x_342_, 3, v_maxRecDepth_332_);
lean_ctor_set(v___x_342_, 4, v_ref_341_);
lean_ctor_set(v___x_342_, 5, v_currNamespace_334_);
lean_ctor_set(v___x_342_, 6, v_openDecls_335_);
lean_ctor_set(v___x_342_, 7, v_initHeartbeats_336_);
lean_ctor_set(v___x_342_, 8, v_maxHeartbeats_337_);
lean_ctor_set(v___x_342_, 9, v_currMacroScope_338_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*10, v_diag_339_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*10 + 1, v_suppressElabErrors_340_);
v___x_343_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v_msg_323_, v___y_324_, v___y_325_, v___x_342_, v___y_327_);
lean_dec_ref_known(v___x_342_, 10);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_344_, v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_ref_344_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_352_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_ctor_set(v___x_357_, 4, v___x_355_);
lean_ctor_set(v___x_357_, 5, v___x_355_);
lean_ctor_set(v___x_357_, 6, v___x_355_);
lean_ctor_set(v___x_357_, 7, v___x_355_);
lean_ctor_set(v___x_357_, 8, v___x_355_);
lean_ctor_set(v___x_357_, 9, v___x_355_);
lean_ctor_set(v___x_357_, 10, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_unsigned_to_nat(32u);
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_361_ = ((size_t)5ULL);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_unsigned_to_nat(32u);
v___x_364_ = lean_mk_empty_array_with_capacity(v___x_363_);
v___x_365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_366_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_362_);
lean_ctor_set(v___x_366_, 3, v___x_362_);
lean_ctor_set_usize(v___x_366_, 4, v___x_361_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = lean_box(1);
v___x_368_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
lean_ctor_set(v___x_370_, 2, v___x_367_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_392_, lean_object* v_declHint_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; lean_object* v_env_397_; uint8_t v___x_398_; 
v___x_396_ = lean_st_ref_get(v___y_394_);
v_env_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_env_397_);
lean_dec(v___x_396_);
v___x_398_ = l_Lean_Name_isAnonymous(v_declHint_393_);
if (v___x_398_ == 0)
{
uint8_t v_isExporting_399_; 
v_isExporting_399_ = lean_ctor_get_uint8(v_env_397_, sizeof(void*)*8);
if (v_isExporting_399_ == 0)
{
lean_object* v___x_400_; 
lean_dec_ref(v_env_397_);
lean_dec(v_declHint_393_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_msg_392_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; uint8_t v___x_402_; 
lean_inc_ref(v_env_397_);
v___x_401_ = l_Lean_Environment_setExporting(v_env_397_, v___x_398_);
lean_inc(v_declHint_393_);
lean_inc_ref(v___x_401_);
v___x_402_ = l_Lean_Environment_contains(v___x_401_, v_declHint_393_, v_isExporting_399_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
lean_dec_ref(v___x_401_);
lean_dec_ref(v_env_397_);
lean_dec(v_declHint_393_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v_msg_392_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_c_409_; lean_object* v___x_410_; 
v___x_404_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_405_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_406_ = l_Lean_Options_empty;
v___x_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_407_, 0, v___x_401_);
lean_ctor_set(v___x_407_, 1, v___x_404_);
lean_ctor_set(v___x_407_, 2, v___x_405_);
lean_ctor_set(v___x_407_, 3, v___x_406_);
lean_inc(v_declHint_393_);
v___x_408_ = l_Lean_MessageData_ofConstName(v_declHint_393_, v___x_398_);
v_c_409_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_409_, 0, v___x_407_);
lean_ctor_set(v_c_409_, 1, v___x_408_);
v___x_410_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_397_, v_declHint_393_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v_env_397_);
lean_dec(v_declHint_393_);
v___x_411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_c_409_);
v___x_413_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = l_Lean_MessageData_note(v___x_414_);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v_msg_392_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
else
{
lean_object* v_val_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_453_; 
v_val_418_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_453_ == 0)
{
v___x_420_ = v___x_410_;
v_isShared_421_ = v_isSharedCheck_453_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_val_418_);
lean_dec(v___x_410_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_453_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_mod_425_; uint8_t v___x_426_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_Environment_header(v_env_397_);
lean_dec_ref(v_env_397_);
v___x_424_ = l_Lean_EnvironmentHeader_moduleNames(v___x_423_);
v_mod_425_ = lean_array_get(v___x_422_, v___x_424_, v_val_418_);
lean_dec(v_val_418_);
lean_dec_ref(v___x_424_);
v___x_426_ = l_Lean_isPrivateName(v_declHint_393_);
lean_dec(v_declHint_393_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_427_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_c_409_);
v___x_429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_MessageData_ofName(v_mod_425_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_MessageData_note(v___x_434_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v_msg_392_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 0);
lean_ctor_set(v___x_420_, 0, v___x_436_);
v___x_438_ = v___x_420_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_c_409_);
v___x_442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_MessageData_ofName(v_mod_425_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_MessageData_note(v___x_447_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v_msg_392_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 0);
lean_ctor_set(v___x_420_, 0, v___x_449_);
v___x_451_ = v___x_420_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_454_; 
lean_dec_ref(v_env_397_);
lean_dec(v_declHint_393_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_msg_392_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_455_, lean_object* v_declHint_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_455_, v_declHint_456_, v___y_457_);
lean_dec(v___y_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_460_, lean_object* v_declHint_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v___x_467_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_460_, v_declHint_461_, v___y_465_);
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = l_Lean_unknownIdentifierMessageTag;
v___x_473_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_a_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_478_, lean_object* v_declHint_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_478_, v_declHint_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_486_, lean_object* v_msg_487_, lean_object* v_declHint_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v_a_495_; lean_object* v___x_496_; 
v___x_494_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_487_, v_declHint_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v___x_496_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_486_, v_a_495_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_497_, lean_object* v_msg_498_, lean_object* v_declHint_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_497_, v_msg_498_, v_declHint_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v_ref_497_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_508_ = l_Lean_stringToMessageData(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_509_, lean_object* v_constName_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_516_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_517_ = 0;
lean_inc(v_constName_510_);
v___x_518_ = l_Lean_MessageData_ofConstName(v_constName_510_, v___x_517_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_516_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_509_, v___x_521_, v_constName_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_523_, lean_object* v_constName_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_523_, v_constName_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v_ref_523_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(lean_object* v_constName_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_ref_537_; lean_object* v___x_538_; 
v_ref_537_ = lean_ctor_get(v___y_534_, 4);
v___x_538_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_537_, v_constName_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg___boxed(lean_object* v_constName_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(lean_object* v_constName_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; lean_object* v_env_553_; uint8_t v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_st_ref_get(v___y_550_);
v_env_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_ref(v_env_553_);
lean_dec(v___x_552_);
v___x_554_ = 0;
lean_inc(v_constName_546_);
v___x_555_ = l_Lean_Environment_find_x3f(v_env_553_, v_constName_546_, v___x_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_556_;
}
else
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_constName_546_);
v_val_557_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_555_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v___x_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_val_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0___boxed(lean_object* v_constName_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_constName_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(lean_object* v_structName_575_, lean_object* v_field_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
if (lean_obj_tag(v_field_576_) == 1)
{
lean_object* v_pre_582_; 
v_pre_582_ = lean_ctor_get(v_field_576_, 0);
if (lean_obj_tag(v_pre_582_) == 0)
{
lean_object* v_str_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_str_583_ = lean_ctor_get(v_field_576_, 1);
lean_inc_ref(v_str_583_);
lean_dec_ref_known(v_field_576_, 2);
v___x_584_ = lean_box(0);
v___x_585_ = l_Lean_Name_str___override(v___x_584_, v_str_583_);
v___x_586_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_structName_575_, v___x_585_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_586_;
}
else
{
lean_object* v_str_587_; lean_object* v___x_588_; 
lean_inc(v_pre_582_);
v_str_587_ = lean_ctor_get(v_field_576_, 1);
lean_inc_ref(v_str_587_);
lean_dec_ref_known(v_field_576_, 2);
lean_inc(v_structName_575_);
v___x_588_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_575_, v_pre_582_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v_fst_590_ = lean_ctor_get(v_a_589_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v_a_589_, 1);
lean_inc(v_snd_591_);
lean_dec(v_a_589_);
v___x_592_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0(v_snd_591_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = l_Lean_ConstantInfo_type(v_a_593_);
lean_dec(v_a_593_);
v___x_595_ = l_Lean_Expr_getForallBody(v___x_594_);
lean_dec_ref(v___x_594_);
if (lean_obj_tag(v___x_595_) == 4)
{
lean_object* v_declName_596_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___x_623_; lean_object* v_env_624_; uint8_t v___x_625_; 
v_declName_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc_n(v_declName_596_, 2);
lean_dec_ref_known(v___x_595_, 2);
v___x_623_ = lean_st_ref_get(v_a_580_);
v_env_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_env_624_);
lean_dec(v___x_623_);
v___x_625_ = l_Lean_isStructure(v_env_624_, v_declName_596_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_inc(v_fst_590_);
v___x_626_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_590_, v_structName_575_, lean_box(0), v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref_known(v___x_626_, 1);
v___y_598_ = v_a_577_;
v___y_599_ = v_a_578_;
v___y_600_ = v_a_579_;
v___y_601_ = v_a_580_;
goto v___jp_597_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_declName_596_);
lean_dec(v_fst_590_);
lean_dec_ref(v_str_587_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_dec(v_structName_575_);
v___y_598_ = v_a_577_;
v___y_599_ = v_a_578_;
v___y_600_ = v_a_579_;
v___y_601_ = v_a_580_;
goto v___jp_597_;
}
v___jp_597_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
v___x_603_ = l_Lean_Name_str___override(v___x_602_, v_str_587_);
v___x_604_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName(v_declName_596_, v___x_603_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_622_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_622_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_622_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_622_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_621_; 
v_fst_609_ = lean_ctor_get(v_a_605_, 0);
v_snd_610_ = lean_ctor_get(v_a_605_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_621_ == 0)
{
v___x_612_ = v_a_605_;
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_609_);
lean_dec(v_a_605_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = l_Lean_Name_append(v_fst_590_, v_fst_609_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_snd_610_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_616_);
v___x_618_ = v___x_607_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
else
{
lean_dec(v_fst_590_);
return v___x_604_;
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v___x_595_);
lean_dec_ref(v_str_587_);
v___x_635_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___lam__0(v_fst_590_, v_structName_575_, lean_box(0), v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_635_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_fst_590_);
lean_dec_ref(v_str_587_);
lean_dec(v_structName_575_);
v_a_636_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_592_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_592_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_dec_ref(v_str_587_);
lean_dec(v_structName_575_);
return v___x_588_;
}
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_field_576_);
lean_dec(v_structName_575_);
v___x_644_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___closed__1);
v___x_645_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2___redArg(v___x_644_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField___boxed(lean_object* v_structName_646_, lean_object* v_field_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_646_, v_field_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(lean_object* v_00_u03b1_654_, lean_object* v_constName_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___redArg(v_constName_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0___boxed(lean_object* v_00_u03b1_662_, lean_object* v_constName_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0(v_00_u03b1_662_, v_constName_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_670_, lean_object* v_ref_671_, lean_object* v_constName_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg(v_ref_671_, v_constName_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_679_, lean_object* v_ref_680_, lean_object* v_constName_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1(v_00_u03b1_679_, v_ref_680_, v_constName_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v_ref_680_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_688_, lean_object* v_ref_689_, lean_object* v_msg_690_, lean_object* v_declHint_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_689_, v_msg_690_, v_declHint_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_698_, lean_object* v_ref_699_, lean_object* v_msg_700_, lean_object* v_declHint_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_698_, v_ref_699_, v_msg_700_, v_declHint_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v_ref_699_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_708_, lean_object* v_declHint_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_708_, v_declHint_709_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_716_, lean_object* v_declHint_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_716_, v_declHint_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_724_, lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_725_, v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_733_, lean_object* v_ref_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_733_, v_ref_734_, v_msg_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v_ref_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(lean_object* v_e_742_, lean_object* v___y_743_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Expr_hasMVar(v_e_742_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v_e_742_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; lean_object* v_mctx_748_; lean_object* v___x_749_; lean_object* v_fst_750_; lean_object* v_snd_751_; lean_object* v___x_752_; lean_object* v_cache_753_; lean_object* v_zetaDeltaFVarIds_754_; lean_object* v_postponed_755_; lean_object* v_diag_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_765_; 
v___x_747_ = lean_st_ref_get(v___y_743_);
v_mctx_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc_ref(v_mctx_748_);
lean_dec(v___x_747_);
v___x_749_ = l_Lean_instantiateMVarsCore(v_mctx_748_, v_e_742_);
v_fst_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_fst_750_);
v_snd_751_ = lean_ctor_get(v___x_749_, 1);
lean_inc(v_snd_751_);
lean_dec_ref(v___x_749_);
v___x_752_ = lean_st_ref_take(v___y_743_);
v_cache_753_ = lean_ctor_get(v___x_752_, 1);
v_zetaDeltaFVarIds_754_ = lean_ctor_get(v___x_752_, 2);
v_postponed_755_ = lean_ctor_get(v___x_752_, 3);
v_diag_756_ = lean_ctor_get(v___x_752_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_752_, 0);
lean_dec(v_unused_766_);
v___x_758_ = v___x_752_;
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_diag_756_);
lean_inc(v_postponed_755_);
lean_inc(v_zetaDeltaFVarIds_754_);
lean_inc(v_cache_753_);
lean_dec(v___x_752_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_snd_751_);
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_snd_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_cache_753_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_zetaDeltaFVarIds_754_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_postponed_755_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_diag_756_);
v___x_761_ = v_reuseFailAlloc_764_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_st_ref_put(v___y_743_, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v_fst_750_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg___boxed(lean_object* v_e_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_767_, v___y_768_);
lean_dec(v___y_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(lean_object* v_e_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_e_771_, v___y_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___boxed(lean_object* v_e_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5(v_e_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
v___x_797_ = lean_apply_7(v_x_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, lean_box(0));
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed(lean_object* v_x_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0(v_x_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(lean_object* v_lctx_807_, lean_object* v_localInsts_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___f_817_; lean_object* v___x_818_; 
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_817_, 0, v_x_809_);
lean_closure_set(v___f_817_, 1, v___y_810_);
lean_closure_set(v___f_817_, 2, v___y_811_);
v___x_818_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_807_, v_localInsts_808_, v___f_817_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_818_) == 0)
{
return v___x_818_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg___boxed(lean_object* v_lctx_827_, lean_object* v_localInsts_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_827_, v_localInsts_828_, v_x_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(lean_object* v_00_u03b1_838_, lean_object* v_lctx_839_, lean_object* v_localInsts_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___redArg(v_lctx_839_, v_localInsts_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed(lean_object* v_00_u03b1_850_, lean_object* v_lctx_851_, lean_object* v_localInsts_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7(v_00_u03b1_850_, v_lctx_851_, v_localInsts_852_, v_x_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl(lean_box(0), v_x_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_870_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_870_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg___boxed(lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(lean_object* v_00_u03b1_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v_x_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___boxed(lean_object* v_00_u03b1_906_, lean_object* v_x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8(v_00_u03b1_906_, v_x_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_915_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6(void){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Array_mkArray0(lean_box(0));
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(lean_object* v_structName_944_, lean_object* v_source_x3f_945_, lean_object* v_fields_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
if (lean_obj_tag(v_source_x3f_945_) == 0)
{
lean_object* v_ref_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_ref_954_ = lean_ctor_get(v___y_951_, 4);
v___x_955_ = 0;
v___x_956_ = l_Lean_SourceInfo_fromRef(v_ref_954_, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_956_, 8);
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_956_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_961_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_962_, 0, v___x_956_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_965_ = l_Lean_Syntax_SepArray_ofElems(v___x_964_, v_fields_946_);
v___x_966_ = l_Array_append___redArg(v___x_961_, v___x_965_);
lean_dec_ref(v___x_965_);
v___x_967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_967_, 0, v___x_956_);
lean_ctor_set(v___x_967_, 1, v___x_960_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
v___x_968_ = l_Lean_Syntax_node1(v___x_956_, v___x_963_, v___x_967_);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_962_);
v___x_970_ = l_Lean_Syntax_node1(v___x_956_, v___x_969_, v___x_962_);
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_956_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_mkCIdent(v_structName_944_);
v___x_974_ = l_Lean_Syntax_node2(v___x_956_, v___x_960_, v___x_972_, v___x_973_);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_956_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_Syntax_node6(v___x_956_, v___x_957_, v___x_959_, v___x_962_, v___x_968_, v___x_970_, v___x_974_, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
else
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1014_; 
v_val_979_ = lean_ctor_get(v_source_x3f_945_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_source_x3f_945_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_981_ = v_source_x3f_945_;
v_isShared_982_ = v_isSharedCheck_1014_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v_source_x3f_945_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1014_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_ref_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_ref_983_ = lean_ctor_get(v___y_951_, 4);
v___x_984_ = 0;
v___x_985_ = l_Lean_SourceInfo_fromRef(v_ref_983_, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_985_, 11);
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_985_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_990_ = l_Lean_Syntax_node1(v___x_985_, v___x_989_, v_val_979_);
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_985_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Syntax_node2(v___x_985_, v___x_989_, v___x_990_, v___x_992_);
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_997_ = l_Lean_Syntax_SepArray_ofElems(v___x_996_, v_fields_946_);
v___x_998_ = l_Array_append___redArg(v___x_995_, v___x_997_);
lean_dec_ref(v___x_997_);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_985_);
lean_ctor_set(v___x_999_, 1, v___x_989_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = l_Lean_Syntax_node1(v___x_985_, v___x_994_, v___x_999_);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1002_, 0, v___x_985_);
lean_ctor_set(v___x_1002_, 1, v___x_989_);
lean_ctor_set(v___x_1002_, 2, v___x_995_);
v___x_1003_ = l_Lean_Syntax_node1(v___x_985_, v___x_1001_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_985_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_mkCIdent(v_structName_944_);
v___x_1007_ = l_Lean_Syntax_node2(v___x_985_, v___x_989_, v___x_1005_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_985_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_node6(v___x_985_, v___x_986_, v___x_988_, v___x_993_, v___x_1000_, v___x_1003_, v___x_1007_, v___x_1009_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 0, v___x_1010_);
v___x_1012_ = v___x_981_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed(lean_object* v_structName_1015_, lean_object* v_source_x3f_1016_, lean_object* v_fields_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_1015_, v_source_x3f_1016_, v_fields_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_fields_1017_);
return v_res_1025_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_1043_ = l_String_toRawSubstring_x27(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(lean_object* v_a_1093_, lean_object* v_structName_1094_, lean_object* v_____r_1095_, lean_object* v_source_x3f_1096_, lean_object* v_seenFields_1097_, lean_object* v_fields_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_toCold_1106_; lean_object* v_value_1107_; lean_object* v_ref_1108_; lean_object* v_currMacroScope_1109_; lean_object* v_quotContext_1110_; lean_object* v_ref_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_toCold_1106_ = lean_ctor_get(v___y_1103_, 0);
v_value_1107_ = lean_ctor_get(v_a_1093_, 2);
lean_inc(v_value_1107_);
lean_dec_ref(v_a_1093_);
v_ref_1108_ = lean_ctor_get(v___y_1103_, 4);
v_currMacroScope_1109_ = lean_ctor_get(v___y_1103_, 9);
v_quotContext_1110_ = lean_ctor_get(v_toCold_1106_, 2);
v_ref_1111_ = l_Lean_replaceRef(v_value_1107_, v_ref_1108_);
v___x_1112_ = 0;
v___x_1113_ = l_Lean_SourceInfo_fromRef(v_ref_1111_, v___x_1112_);
lean_dec(v_ref_1111_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__1));
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_1113_, 8);
v___x_1117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1113_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_1119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_1120_ = lean_box(0);
lean_inc(v_currMacroScope_1109_);
lean_inc(v_quotContext_1110_);
v___x_1121_ = l_Lean_addMacroScope(v_quotContext_1110_, v___x_1120_, v_currMacroScope_1109_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_1123_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1113_);
lean_ctor_set(v___x_1123_, 1, v___x_1119_);
lean_ctor_set(v___x_1123_, 2, v___x_1121_);
lean_ctor_set(v___x_1123_, 3, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node1(v___x_1113_, v___x_1118_, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_node2(v___x_1113_, v___x_1115_, v___x_1117_, v___x_1124_);
v___x_1126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_1127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1113_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_1129_ = l_Lean_mkCIdent(v_structName_1094_);
lean_inc(v___x_1129_);
v___x_1130_ = l_Lean_Syntax_node1(v___x_1113_, v___x_1128_, v___x_1129_);
v___x_1131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_1132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1113_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
lean_inc_ref(v___x_1127_);
v___x_1133_ = l_Lean_Syntax_node5(v___x_1113_, v___x_1114_, v___x_1125_, v_value_1107_, v___x_1127_, v___x_1130_, v___x_1132_);
if (lean_obj_tag(v_source_x3f_1096_) == 1)
{
lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1165_; 
v_val_1134_ = lean_ctor_get(v_source_x3f_1096_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_source_x3f_1096_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1136_ = v_source_x3f_1096_;
v_isShared_1137_ = v_isSharedCheck_1165_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_dec(v_source_x3f_1096_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1165_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_1139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_1113_, 10);
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1113_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__27));
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1113_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_Syntax_node3(v___x_1113_, v___x_1128_, v___x_1133_, v___x_1142_, v_val_1134_);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
v___x_1145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1113_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node2(v___x_1113_, v___x_1128_, v___x_1143_, v___x_1145_);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_1148_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_1149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1113_);
lean_ctor_set(v___x_1149_, 1, v___x_1128_);
lean_ctor_set(v___x_1149_, 2, v___x_1148_);
lean_inc_ref(v___x_1149_);
v___x_1150_ = l_Lean_Syntax_node1(v___x_1113_, v___x_1147_, v___x_1149_);
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_1152_ = l_Lean_Syntax_node1(v___x_1113_, v___x_1151_, v___x_1149_);
v___x_1153_ = l_Lean_Syntax_node2(v___x_1113_, v___x_1128_, v___x_1127_, v___x_1129_);
v___x_1154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_1155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1113_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node6(v___x_1113_, v___x_1138_, v___x_1140_, v___x_1146_, v___x_1150_, v___x_1152_, v___x_1153_, v___x_1155_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1156_);
v___x_1158_ = v___x_1136_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_seenFields_1097_);
lean_ctor_set(v___x_1160_, 1, v_fields_1098_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1158_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1159_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v___x_1129_);
lean_dec_ref_known(v___x_1127_, 2);
lean_dec(v___x_1113_);
lean_dec(v_source_x3f_1096_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1133_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_seenFields_1097_);
lean_ctor_set(v___x_1168_, 1, v_fields_1098_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1166_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1167_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___boxed(lean_object* v_a_1172_, lean_object* v_structName_1173_, lean_object* v_____r_1174_, lean_object* v_source_x3f_1175_, lean_object* v_seenFields_1176_, lean_object* v_fields_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_1172_, v_structName_1173_, v_____r_1174_, v_source_x3f_1175_, v_seenFields_1176_, v_fields_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(lean_object* v_opts_1186_, lean_object* v_opt_1187_){
_start:
{
lean_object* v_name_1188_; lean_object* v_defValue_1189_; lean_object* v_map_1190_; lean_object* v___x_1191_; 
v_name_1188_ = lean_ctor_get(v_opt_1187_, 0);
v_defValue_1189_ = lean_ctor_get(v_opt_1187_, 1);
v_map_1190_ = lean_ctor_get(v_opts_1186_, 0);
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1190_, v_name_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_unbox(v_defValue_1189_);
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; 
v_val_1193_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1191_, 1);
if (lean_obj_tag(v_val_1193_) == 1)
{
uint8_t v_v_1194_; 
v_v_1194_ = lean_ctor_get_uint8(v_val_1193_, 0);
lean_dec_ref_known(v_val_1193_, 0);
return v_v_1194_;
}
else
{
uint8_t v___x_1195_; 
lean_dec(v_val_1193_);
v___x_1195_ = lean_unbox(v_defValue_1189_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_opts_1196_, lean_object* v_opt_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_opts_1196_, v_opt_1197_);
lean_dec_ref(v_opt_1197_);
lean_dec_ref(v_opts_1196_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(1);
v___x_1201_ = l_Lean_MessageData_ofFormat(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__2));
v___x_1206_ = l_Lean_MessageData_ofFormat(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
return v_x_1207_;
}
else
{
lean_object* v_head_1209_; lean_object* v_tail_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1232_; 
v_head_1209_ = lean_ctor_get(v_x_1208_, 0);
v_tail_1210_ = lean_ctor_get(v_x_1208_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1212_ = v_x_1208_;
v_isShared_1213_ = v_isSharedCheck_1232_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_tail_1210_);
lean_inc(v_head_1209_);
lean_dec(v_x_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1232_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_before_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1230_; 
v_before_1214_ = lean_ctor_get(v_head_1209_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_head_1209_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_head_1209_, 1);
lean_dec(v_unused_1231_);
v___x_1216_ = v_head_1209_;
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_before_1214_);
lean_dec(v_head_1209_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 7);
lean_ctor_set(v___x_1216_, 1, v___x_1218_);
lean_ctor_set(v___x_1216_, 0, v_x_1207_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_x_1207_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__3);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 7);
lean_ctor_set(v___x_1212_, 1, v___x_1221_);
lean_ctor_set(v___x_1212_, 0, v___x_1220_);
v___x_1223_ = v___x_1212_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = l_Lean_MessageData_ofSyntax(v_before_1214_);
v___x_1225_ = l_Lean_indentD(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1223_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v_x_1207_ = v___x_1226_;
v_x_1208_ = v_tail_1210_;
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
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__1));
v___x_1237_ = l_Lean_MessageData_ofFormat(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(lean_object* v_msgData_1238_, lean_object* v_macroStack_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_options_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_options_1242_ = lean_ctor_get(v___y_1240_, 1);
v___x_1243_ = l_Lean_Elab_pp_macroStack;
v___x_1244_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_options_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec(v_macroStack_1239_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_msgData_1238_);
return v___x_1245_;
}
else
{
if (lean_obj_tag(v_macroStack_1239_) == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_msgData_1238_);
return v___x_1246_;
}
else
{
lean_object* v_head_1247_; lean_object* v_after_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1263_; 
v_head_1247_ = lean_ctor_get(v_macroStack_1239_, 0);
lean_inc(v_head_1247_);
v_after_1248_ = lean_ctor_get(v_head_1247_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_head_1247_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v_head_1247_, 0);
lean_dec(v_unused_1264_);
v___x_1250_ = v_head_1247_;
v_isShared_1251_ = v_isSharedCheck_1263_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_after_1248_);
lean_dec(v_head_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1263_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20___closed__0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 7);
lean_ctor_set(v___x_1250_, 1, v___x_1252_);
lean_ctor_set(v___x_1250_, 0, v_msgData_1238_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_msgData_1238_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_msgData_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1255_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___closed__2);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_MessageData_ofSyntax(v_after_1248_);
v___x_1258_ = l_Lean_indentD(v___x_1257_);
v_msgData_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1259_, 0, v___x_1256_);
lean_ctor_set(v_msgData_1259_, 1, v___x_1258_);
v___x_1260_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15_spec__20(v_msgData_1259_, v_macroStack_1239_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg___boxed(lean_object* v_msgData_1265_, lean_object* v_macroStack_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_1265_, v_macroStack_1266_, v___y_1267_);
lean_dec_ref(v___y_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_ref_1278_; lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v_macroStack_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
v_ref_1278_ = lean_ctor_get(v___y_1275_, 4);
v___x_1279_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v_msg_1270_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v_macroStack_1281_ = lean_ctor_get(v___y_1271_, 1);
v___x_1282_ = l_Lean_Elab_getBetterRef(v_ref_1278_, v_macroStack_1281_);
lean_inc(v_macroStack_1281_);
v___x_1283_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_a_1280_, v_macroStack_1281_, v___y_1275_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1282_);
lean_ctor_set(v___x_1288_, 1, v_a_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg___boxed(lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(lean_object* v_ref_1302_, lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_toCold_1311_; lean_object* v_options_1312_; lean_object* v_currRecDepth_1313_; lean_object* v_maxRecDepth_1314_; lean_object* v_ref_1315_; lean_object* v_currNamespace_1316_; lean_object* v_openDecls_1317_; lean_object* v_initHeartbeats_1318_; lean_object* v_maxHeartbeats_1319_; lean_object* v_currMacroScope_1320_; uint8_t v_diag_1321_; uint8_t v_suppressElabErrors_1322_; lean_object* v_ref_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_toCold_1311_ = lean_ctor_get(v___y_1308_, 0);
v_options_1312_ = lean_ctor_get(v___y_1308_, 1);
v_currRecDepth_1313_ = lean_ctor_get(v___y_1308_, 2);
v_maxRecDepth_1314_ = lean_ctor_get(v___y_1308_, 3);
v_ref_1315_ = lean_ctor_get(v___y_1308_, 4);
v_currNamespace_1316_ = lean_ctor_get(v___y_1308_, 5);
v_openDecls_1317_ = lean_ctor_get(v___y_1308_, 6);
v_initHeartbeats_1318_ = lean_ctor_get(v___y_1308_, 7);
v_maxHeartbeats_1319_ = lean_ctor_get(v___y_1308_, 8);
v_currMacroScope_1320_ = lean_ctor_get(v___y_1308_, 9);
v_diag_1321_ = lean_ctor_get_uint8(v___y_1308_, sizeof(void*)*10);
v_suppressElabErrors_1322_ = lean_ctor_get_uint8(v___y_1308_, sizeof(void*)*10 + 1);
v_ref_1323_ = l_Lean_replaceRef(v_ref_1302_, v_ref_1315_);
lean_inc(v_currMacroScope_1320_);
lean_inc(v_maxHeartbeats_1319_);
lean_inc(v_initHeartbeats_1318_);
lean_inc(v_openDecls_1317_);
lean_inc(v_currNamespace_1316_);
lean_inc(v_maxRecDepth_1314_);
lean_inc(v_currRecDepth_1313_);
lean_inc_ref(v_options_1312_);
lean_inc_ref(v_toCold_1311_);
v___x_1324_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1324_, 0, v_toCold_1311_);
lean_ctor_set(v___x_1324_, 1, v_options_1312_);
lean_ctor_set(v___x_1324_, 2, v_currRecDepth_1313_);
lean_ctor_set(v___x_1324_, 3, v_maxRecDepth_1314_);
lean_ctor_set(v___x_1324_, 4, v_ref_1323_);
lean_ctor_set(v___x_1324_, 5, v_currNamespace_1316_);
lean_ctor_set(v___x_1324_, 6, v_openDecls_1317_);
lean_ctor_set(v___x_1324_, 7, v_initHeartbeats_1318_);
lean_ctor_set(v___x_1324_, 8, v_maxHeartbeats_1319_);
lean_ctor_set(v___x_1324_, 9, v_currMacroScope_1320_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*10, v_diag_1321_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*10 + 1, v_suppressElabErrors_1322_);
v___x_1325_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___x_1324_, v___y_1309_);
lean_dec_ref_known(v___x_1324_, 10);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg___boxed(lean_object* v_ref_1326_, lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1326_, v_msg_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v_ref_1326_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(lean_object* v_msg_1336_, lean_object* v_declHint_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v_env_1341_; uint8_t v___x_1342_; 
v___x_1340_ = lean_st_ref_get(v___y_1338_);
v_env_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc_ref(v_env_1341_);
lean_dec(v___x_1340_);
v___x_1342_ = l_Lean_Name_isAnonymous(v_declHint_1337_);
if (v___x_1342_ == 0)
{
uint8_t v_isExporting_1343_; 
v_isExporting_1343_ = lean_ctor_get_uint8(v_env_1341_, sizeof(void*)*8);
if (v_isExporting_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v_env_1341_);
lean_dec(v_declHint_1337_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_msg_1336_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
lean_inc_ref(v_env_1341_);
v___x_1345_ = l_Lean_Environment_setExporting(v_env_1341_, v___x_1342_);
lean_inc(v_declHint_1337_);
lean_inc_ref(v___x_1345_);
v___x_1346_ = l_Lean_Environment_contains(v___x_1345_, v_declHint_1337_, v_isExporting_1343_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref(v___x_1345_);
lean_dec_ref(v_env_1341_);
lean_dec(v_declHint_1337_);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_msg_1336_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_c_1355_; lean_object* v___x_1356_; 
v___x_1348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1349_ = lean_unsigned_to_nat(32u);
v___x_1350_ = lean_mk_empty_array_with_capacity(v___x_1349_);
lean_dec_ref(v___x_1350_);
v___x_1351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1352_ = l_Lean_Options_empty;
v___x_1353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1345_);
lean_ctor_set(v___x_1353_, 1, v___x_1348_);
lean_ctor_set(v___x_1353_, 2, v___x_1351_);
lean_ctor_set(v___x_1353_, 3, v___x_1352_);
lean_inc(v_declHint_1337_);
v___x_1354_ = l_Lean_MessageData_ofConstName(v_declHint_1337_, v___x_1342_);
v_c_1355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1355_, 0, v___x_1353_);
lean_ctor_set(v_c_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1341_, v_declHint_1337_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v_env_1341_);
lean_dec(v_declHint_1337_);
v___x_1357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v_c_1355_);
v___x_1359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_MessageData_note(v___x_1360_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_msg_1336_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
else
{
lean_object* v_val_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1399_; 
v_val_1364_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1366_ = v___x_1356_;
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_val_1364_);
lean_dec(v___x_1356_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_mod_1371_; uint8_t v___x_1372_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Lean_Environment_header(v_env_1341_);
lean_dec_ref(v_env_1341_);
v___x_1370_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1369_);
v_mod_1371_ = lean_array_get(v___x_1368_, v___x_1370_, v_val_1364_);
lean_dec(v_val_1364_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = l_Lean_isPrivateName(v_declHint_1337_);
lean_dec(v_declHint_1337_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v_c_1355_);
v___x_1375_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_MessageData_ofName(v_mod_1371_);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_note(v___x_1380_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_msg_1336_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1382_);
v___x_1384_ = v___x_1366_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_c_1355_);
v___x_1388_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = l_Lean_MessageData_ofName(v_mod_1371_);
v___x_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_MessageData_note(v___x_1393_);
v___x_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_msg_1336_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1395_);
v___x_1397_ = v___x_1366_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1400_; 
lean_dec_ref(v_env_1341_);
lean_dec(v_declHint_1337_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_msg_1336_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg___boxed(lean_object* v_msg_1401_, lean_object* v_declHint_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1401_, v_declHint_1402_, v___y_1403_);
lean_dec(v___y_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(lean_object* v_msg_1406_, lean_object* v_declHint_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1425_; 
v___x_1415_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_1406_, v_declHint_1407_, v___y_1413_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1425_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1425_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = l_Lean_unknownIdentifierMessageTag;
v___x_1421_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23___boxed(lean_object* v_msg_1426_, lean_object* v_declHint_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1426_, v_declHint_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(lean_object* v_ref_1436_, lean_object* v_msg_1437_, lean_object* v_declHint_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; 
v___x_1446_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23(v_msg_1437_, v_declHint_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1446_);
v___x_1448_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_1436_, v_a_1447_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg___boxed(lean_object* v_ref_1449_, lean_object* v_msg_1450_, lean_object* v_declHint_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1449_, v_msg_1450_, v_declHint_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v_ref_1449_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(lean_object* v_ref_1460_, lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1469_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1470_ = 0;
lean_inc(v_constName_1461_);
v___x_1471_ = l_Lean_MessageData_ofConstName(v_constName_1461_, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1469_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__13);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_1460_, v___x_1474_, v_constName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_ref_1476_, lean_object* v_constName_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1476_, v_constName_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v_ref_1476_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(lean_object* v_constName_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_ref_1494_; lean_object* v___x_1495_; 
v_ref_1494_ = lean_ctor_get(v___y_1491_, 4);
v___x_1495_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_1494_, v_constName_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg___boxed(lean_object* v_constName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(lean_object* v_constName_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v_env_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_st_ref_get(v___y_1511_);
v_env_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc_ref(v_env_1514_);
lean_dec(v___x_1513_);
v___x_1515_ = 0;
lean_inc(v_constName_1505_);
v___x_1516_ = l_Lean_Environment_find_x3f(v_env_1514_, v_constName_1505_, v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1517_;
}
else
{
lean_object* v_val_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_constName_1505_);
v_val_1518_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1516_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_val_1518_);
lean_dec(v___x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 0);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_val_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2___boxed(lean_object* v_constName_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_constName_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(uint8_t v_suppressElabErrors_1541_, uint8_t v___y_1542_, lean_object* v_x_1543_){
_start:
{
if (lean_obj_tag(v_x_1543_) == 1)
{
lean_object* v_pre_1544_; 
v_pre_1544_ = lean_ctor_get(v_x_1543_, 0);
switch(lean_obj_tag(v_pre_1544_))
{
case 1:
{
lean_object* v_pre_1545_; 
v_pre_1545_ = lean_ctor_get(v_pre_1544_, 0);
switch(lean_obj_tag(v_pre_1545_))
{
case 0:
{
lean_object* v_str_1546_; lean_object* v_str_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_str_1546_ = lean_ctor_get(v_x_1543_, 1);
v_str_1547_ = lean_ctor_get(v_pre_1544_, 1);
v___x_1548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__8));
v___x_1549_ = lean_string_dec_eq(v_str_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__2));
v___x_1551_ = lean_string_dec_eq(v_str_1547_, v___x_1550_);
if (v___x_1551_ == 0)
{
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___x_1553_ = lean_string_dec_eq(v_str_1546_, v___x_1552_);
if (v___x_1553_ == 0)
{
return v___x_1553_;
}
else
{
return v_suppressElabErrors_1541_;
}
}
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__1));
v___x_1555_ = lean_string_dec_eq(v_str_1546_, v___x_1554_);
if (v___x_1555_ == 0)
{
return v___x_1555_;
}
else
{
return v_suppressElabErrors_1541_;
}
}
}
case 1:
{
lean_object* v_pre_1556_; 
v_pre_1556_ = lean_ctor_get(v_pre_1545_, 0);
if (lean_obj_tag(v_pre_1556_) == 0)
{
lean_object* v_str_1557_; lean_object* v_str_1558_; lean_object* v_str_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_str_1557_ = lean_ctor_get(v_x_1543_, 1);
v_str_1558_ = lean_ctor_get(v_pre_1544_, 1);
v_str_1559_ = lean_ctor_get(v_pre_1545_, 1);
v___x_1560_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__2));
v___x_1561_ = lean_string_dec_eq(v_str_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__3));
v___x_1563_ = lean_string_dec_eq(v_str_1558_, v___x_1562_);
if (v___x_1563_ == 0)
{
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__4));
v___x_1565_ = lean_string_dec_eq(v_str_1557_, v___x_1564_);
if (v___x_1565_ == 0)
{
return v___x_1565_;
}
else
{
return v_suppressElabErrors_1541_;
}
}
}
}
else
{
return v___y_1542_;
}
}
default: 
{
return v___y_1542_;
}
}
}
case 0:
{
lean_object* v_str_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_str_1566_ = lean_ctor_get(v_x_1543_, 1);
v___x_1567_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___closed__5));
v___x_1568_ = lean_string_dec_eq(v_str_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
return v___x_1568_;
}
else
{
return v_suppressElabErrors_1541_;
}
}
default: 
{
return v___y_1542_;
}
}
}
else
{
return v___y_1542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1569_, lean_object* v___y_1570_, lean_object* v_x_1571_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1572_; uint8_t v___y_50139__boxed_1573_; uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_suppressElabErrors_boxed_1572_ = lean_unbox(v_suppressElabErrors_1569_);
v___y_50139__boxed_1573_ = lean_unbox(v___y_1570_);
v_res_1574_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0(v_suppressElabErrors_boxed_1572_, v___y_50139__boxed_1573_, v_x_1571_);
lean_dec(v_x_1571_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1576_, lean_object* v_msgData_1577_, uint8_t v_severity_1578_, uint8_t v_isSilent_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; uint8_t v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1622_; uint8_t v___y_1623_; uint8_t v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1648_; uint8_t v___y_1649_; uint8_t v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1658_; uint8_t v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; uint8_t v___y_1662_; uint8_t v___y_1663_; uint8_t v___x_1668_; lean_object* v___y_1670_; uint8_t v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; uint8_t v___y_1674_; uint8_t v___y_1675_; uint8_t v___y_1677_; uint8_t v___x_1691_; 
v___x_1668_ = 2;
v___x_1691_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1578_, v___x_1668_);
if (v___x_1691_ == 0)
{
v___y_1677_ = v___x_1691_;
goto v___jp_1676_;
}
else
{
uint8_t v___x_1692_; 
lean_inc_ref(v_msgData_1577_);
v___x_1692_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1577_);
v___y_1677_ = v___x_1692_;
goto v___jp_1676_;
}
v___jp_1585_:
{
lean_object* v___x_1595_; lean_object* v_currNamespace_1596_; lean_object* v_openDecls_1597_; lean_object* v_env_1598_; lean_object* v_nextMacroScope_1599_; lean_object* v_ngen_1600_; lean_object* v_auxDeclNGen_1601_; lean_object* v_traceState_1602_; lean_object* v_cache_1603_; lean_object* v_messages_1604_; lean_object* v_infoState_1605_; lean_object* v_snapshotTasks_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1620_; 
v___x_1595_ = lean_st_ref_take(v___y_1594_);
v_currNamespace_1596_ = lean_ctor_get(v___y_1593_, 5);
v_openDecls_1597_ = lean_ctor_get(v___y_1593_, 6);
v_env_1598_ = lean_ctor_get(v___x_1595_, 0);
v_nextMacroScope_1599_ = lean_ctor_get(v___x_1595_, 1);
v_ngen_1600_ = lean_ctor_get(v___x_1595_, 2);
v_auxDeclNGen_1601_ = lean_ctor_get(v___x_1595_, 3);
v_traceState_1602_ = lean_ctor_get(v___x_1595_, 4);
v_cache_1603_ = lean_ctor_get(v___x_1595_, 5);
v_messages_1604_ = lean_ctor_get(v___x_1595_, 6);
v_infoState_1605_ = lean_ctor_get(v___x_1595_, 7);
v_snapshotTasks_1606_ = lean_ctor_get(v___x_1595_, 8);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1608_ = v___x_1595_;
v_isShared_1609_ = v_isSharedCheck_1620_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_snapshotTasks_1606_);
lean_inc(v_infoState_1605_);
lean_inc(v_messages_1604_);
lean_inc(v_cache_1603_);
lean_inc(v_traceState_1602_);
lean_inc(v_auxDeclNGen_1601_);
lean_inc(v_ngen_1600_);
lean_inc(v_nextMacroScope_1599_);
lean_inc(v_env_1598_);
lean_dec(v___x_1595_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1620_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_inc(v_openDecls_1597_);
lean_inc(v_currNamespace_1596_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_currNamespace_1596_);
lean_ctor_set(v___x_1610_, 1, v_openDecls_1597_);
v___x_1611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v___y_1589_);
lean_inc_ref(v___y_1590_);
lean_inc_ref(v___y_1591_);
v___x_1612_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1612_, 0, v___y_1591_);
lean_ctor_set(v___x_1612_, 1, v___y_1587_);
lean_ctor_set(v___x_1612_, 2, v___y_1588_);
lean_ctor_set(v___x_1612_, 3, v___y_1590_);
lean_ctor_set(v___x_1612_, 4, v___x_1611_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*5, v___y_1592_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*5 + 1, v___y_1586_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*5 + 2, v_isSilent_1579_);
v___x_1613_ = l_Lean_MessageLog_add(v___x_1612_, v_messages_1604_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 6, v___x_1613_);
v___x_1615_ = v___x_1608_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_env_1598_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_nextMacroScope_1599_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_ngen_1600_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_auxDeclNGen_1601_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_traceState_1602_);
lean_ctor_set(v_reuseFailAlloc_1619_, 5, v_cache_1603_);
lean_ctor_set(v_reuseFailAlloc_1619_, 6, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 7, v_infoState_1605_);
lean_ctor_set(v_reuseFailAlloc_1619_, 8, v_snapshotTasks_1606_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_st_ref_put(v___y_1594_, v___x_1615_);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
}
}
v___jp_1621_:
{
lean_object* v_fileName_1629_; lean_object* v_fileMap_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1646_; 
v_fileName_1629_ = lean_ctor_get(v___y_1625_, 0);
v_fileMap_1630_ = lean_ctor_get(v___y_1625_, 1);
v___x_1631_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1577_);
v___x_1632_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName_spec__2_spec__2(v___x_1631_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_inc_ref_n(v_fileMap_1630_, 2);
v___x_1637_ = l_Lean_FileMap_toPosition(v_fileMap_1630_, v___y_1626_);
lean_dec(v___y_1626_);
v___x_1638_ = l_Lean_FileMap_toPosition(v_fileMap_1630_, v___y_1628_);
lean_dec(v___y_1628_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___x_1640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
if (v___y_1624_ == 0)
{
lean_del_object(v___x_1635_);
lean_dec_ref(v___y_1622_);
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___x_1637_;
v___y_1588_ = v___x_1639_;
v___y_1589_ = v_a_1633_;
v___y_1590_ = v___x_1640_;
v___y_1591_ = v_fileName_1629_;
v___y_1592_ = v___y_1627_;
v___y_1593_ = v___y_1582_;
v___y_1594_ = v___y_1583_;
goto v___jp_1585_;
}
else
{
uint8_t v___x_1641_; 
lean_inc(v_a_1633_);
v___x_1641_ = l_Lean_MessageData_hasTag(v___y_1622_, v_a_1633_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_dec_ref_known(v___x_1639_, 1);
lean_dec_ref(v___x_1637_);
lean_dec(v_a_1633_);
v___x_1642_ = lean_box(0);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1642_);
v___x_1644_ = v___x_1635_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
else
{
lean_del_object(v___x_1635_);
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___x_1637_;
v___y_1588_ = v___x_1639_;
v___y_1589_ = v_a_1633_;
v___y_1590_ = v___x_1640_;
v___y_1591_ = v_fileName_1629_;
v___y_1592_ = v___y_1627_;
v___y_1593_ = v___y_1582_;
v___y_1594_ = v___y_1583_;
goto v___jp_1585_;
}
}
}
}
v___jp_1647_:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Syntax_getTailPos_x3f(v___y_1653_, v___y_1652_);
lean_dec(v___y_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_inc(v___y_1654_);
v___y_1622_ = v___y_1648_;
v___y_1623_ = v___y_1649_;
v___y_1624_ = v___y_1650_;
v___y_1625_ = v___y_1651_;
v___y_1626_ = v___y_1654_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1654_;
goto v___jp_1621_;
}
else
{
lean_object* v_val_1656_; 
v_val_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___y_1622_ = v___y_1648_;
v___y_1623_ = v___y_1649_;
v___y_1624_ = v___y_1650_;
v___y_1625_ = v___y_1651_;
v___y_1626_ = v___y_1654_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v_val_1656_;
goto v___jp_1621_;
}
}
v___jp_1657_:
{
lean_object* v_ref_1664_; lean_object* v___x_1665_; 
v_ref_1664_ = l_Lean_replaceRef(v_ref_1576_, v___y_1661_);
v___x_1665_ = l_Lean_Syntax_getPos_x3f(v_ref_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___y_1648_ = v___y_1658_;
v___y_1649_ = v___y_1663_;
v___y_1650_ = v___y_1659_;
v___y_1651_ = v___y_1660_;
v___y_1652_ = v___y_1662_;
v___y_1653_ = v_ref_1664_;
v___y_1654_ = v___x_1666_;
goto v___jp_1647_;
}
else
{
lean_object* v_val_1667_; 
v_val_1667_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1665_, 1);
v___y_1648_ = v___y_1658_;
v___y_1649_ = v___y_1663_;
v___y_1650_ = v___y_1659_;
v___y_1651_ = v___y_1660_;
v___y_1652_ = v___y_1662_;
v___y_1653_ = v_ref_1664_;
v___y_1654_ = v_val_1667_;
goto v___jp_1647_;
}
}
v___jp_1669_:
{
if (v___y_1675_ == 0)
{
v___y_1658_ = v___y_1670_;
v___y_1659_ = v___y_1671_;
v___y_1660_ = v___y_1672_;
v___y_1661_ = v___y_1673_;
v___y_1662_ = v___y_1674_;
v___y_1663_ = v_severity_1578_;
goto v___jp_1657_;
}
else
{
v___y_1658_ = v___y_1670_;
v___y_1659_ = v___y_1671_;
v___y_1660_ = v___y_1672_;
v___y_1661_ = v___y_1673_;
v___y_1662_ = v___y_1674_;
v___y_1663_ = v___x_1668_;
goto v___jp_1657_;
}
}
v___jp_1676_:
{
if (v___y_1677_ == 0)
{
lean_object* v_toCold_1678_; lean_object* v_options_1679_; lean_object* v_ref_1680_; uint8_t v_suppressElabErrors_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___f_1684_; uint8_t v___x_1685_; uint8_t v___x_1686_; 
v_toCold_1678_ = lean_ctor_get(v___y_1582_, 0);
v_options_1679_ = lean_ctor_get(v___y_1582_, 1);
v_ref_1680_ = lean_ctor_get(v___y_1582_, 4);
v_suppressElabErrors_1681_ = lean_ctor_get_uint8(v___y_1582_, sizeof(void*)*10 + 1);
v___x_1682_ = lean_box(v_suppressElabErrors_1681_);
v___x_1683_ = lean_box(v___y_1677_);
v___f_1684_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1684_, 0, v___x_1682_);
lean_closure_set(v___f_1684_, 1, v___x_1683_);
v___x_1685_ = 1;
v___x_1686_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1578_, v___x_1685_);
if (v___x_1686_ == 0)
{
v___y_1670_ = v___f_1684_;
v___y_1671_ = v_suppressElabErrors_1681_;
v___y_1672_ = v_toCold_1678_;
v___y_1673_ = v_ref_1680_;
v___y_1674_ = v___y_1677_;
v___y_1675_ = v___x_1686_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = l_Lean_warningAsError;
v___x_1688_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4_spec__10(v_options_1679_, v___x_1687_);
v___y_1670_ = v___f_1684_;
v___y_1671_ = v_suppressElabErrors_1681_;
v___y_1672_ = v_toCold_1678_;
v___y_1673_ = v_ref_1680_;
v___y_1674_ = v___y_1677_;
v___y_1675_ = v___x_1688_;
goto v___jp_1669_;
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref(v_msgData_1577_);
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1693_, lean_object* v_msgData_1694_, lean_object* v_severity_1695_, lean_object* v_isSilent_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v_severity_boxed_1702_; uint8_t v_isSilent_boxed_1703_; lean_object* v_res_1704_; 
v_severity_boxed_1702_ = lean_unbox(v_severity_1695_);
v_isSilent_boxed_1703_ = lean_unbox(v_isSilent_1696_);
v_res_1704_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1693_, v_msgData_1694_, v_severity_boxed_1702_, v_isSilent_boxed_1703_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v_ref_1693_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(lean_object* v_msgData_1705_, uint8_t v_severity_1706_, uint8_t v_isSilent_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_ref_1715_; lean_object* v___x_1716_; 
v_ref_1715_ = lean_ctor_get(v___y_1712_, 4);
v___x_1716_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1715_, v_msgData_1705_, v_severity_1706_, v_isSilent_1707_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1717_, lean_object* v_severity_1718_, lean_object* v_isSilent_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v_severity_boxed_1727_; uint8_t v_isSilent_boxed_1728_; lean_object* v_res_1729_; 
v_severity_boxed_1727_ = lean_unbox(v_severity_1718_);
v_isSilent_boxed_1728_ = lean_unbox(v_isSilent_1719_);
v_res_1729_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1717_, v_severity_boxed_1727_, v_isSilent_boxed_1728_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(lean_object* v_msgData_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = 2;
v___x_1739_ = 0;
v___x_1740_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1_spec__6(v_msgData_1730_, v___x_1738_, v___x_1739_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1___boxed(lean_object* v_msgData_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v_msgData_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(lean_object* v_ref_1750_, lean_object* v_msgData_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = 2;
v___x_1760_ = 0;
v___x_1761_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_1750_, v_msgData_1751_, v___x_1759_, v___x_1760_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0___boxed(lean_object* v_ref_1762_, lean_object* v_msgData_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1762_, v_msgData_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v_ref_1762_);
return v_res_1771_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__0));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(lean_object* v_ex_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
if (lean_obj_tag(v_ex_1775_) == 0)
{
lean_object* v_ref_1783_; lean_object* v_msg_1784_; lean_object* v___x_1785_; 
v_ref_1783_ = lean_ctor_get(v_ex_1775_, 0);
lean_inc(v_ref_1783_);
v_msg_1784_ = lean_ctor_get(v_ex_1775_, 1);
lean_inc_ref(v_msg_1784_);
lean_dec_ref_known(v_ex_1775_, 2);
v___x_1785_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0(v_ref_1783_, v_msg_1784_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v_ref_1783_);
return v___x_1785_;
}
else
{
lean_object* v_id_1786_; uint8_t v___y_1788_; uint8_t v___x_1810_; 
v_id_1786_ = lean_ctor_get(v_ex_1775_, 0);
lean_inc(v_id_1786_);
v___x_1810_ = l_Lean_Elab_isAbortExceptionId(v_id_1786_);
if (v___x_1810_ == 0)
{
uint8_t v___x_1811_; 
v___x_1811_ = l_Lean_Exception_isInterrupt(v_ex_1775_);
lean_dec_ref_known(v_ex_1775_, 2);
v___y_1788_ = v___x_1811_;
goto v___jp_1787_;
}
else
{
lean_dec_ref_known(v_ex_1775_, 2);
v___y_1788_ = v___x_1810_;
goto v___jp_1787_;
}
v___jp_1787_:
{
if (v___y_1788_ == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_InternalExceptionId_getName(v_id_1786_);
lean_dec(v_id_1786_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v___x_1791_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___closed__1);
v___x_1792_ = l_Lean_MessageData_ofName(v_a_1790_);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__1(v___x_1793_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
return v___x_1794_;
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1807_; 
v_a_1795_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1797_ = v___x_1789_;
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1789_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_ref_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v_ref_1799_ = lean_ctor_get(v___y_1780_, 4);
v___x_1800_ = lean_io_error_to_string(v_a_1795_);
v___x_1801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
v___x_1802_ = l_Lean_MessageData_ofFormat(v___x_1801_);
lean_inc(v_ref_1799_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_ref_1799_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1803_);
v___x_1805_ = v___x_1797_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_id_1786_);
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0___boxed(lean_object* v_ex_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v_ex_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(lean_object* v_t_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v_infoState_1825_; uint8_t v_enabled_1826_; 
v___x_1824_ = lean_st_ref_get(v___y_1822_);
v_infoState_1825_ = lean_ctor_get(v___x_1824_, 7);
lean_inc_ref(v_infoState_1825_);
lean_dec(v___x_1824_);
v_enabled_1826_ = lean_ctor_get_uint8(v_infoState_1825_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1825_);
if (v_enabled_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_t_1821_);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; lean_object* v_infoState_1830_; lean_object* v_env_1831_; lean_object* v_nextMacroScope_1832_; lean_object* v_ngen_1833_; lean_object* v_auxDeclNGen_1834_; lean_object* v_traceState_1835_; lean_object* v_cache_1836_; lean_object* v_messages_1837_; lean_object* v_snapshotTasks_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1860_; 
v___x_1829_ = lean_st_ref_take(v___y_1822_);
v_infoState_1830_ = lean_ctor_get(v___x_1829_, 7);
v_env_1831_ = lean_ctor_get(v___x_1829_, 0);
v_nextMacroScope_1832_ = lean_ctor_get(v___x_1829_, 1);
v_ngen_1833_ = lean_ctor_get(v___x_1829_, 2);
v_auxDeclNGen_1834_ = lean_ctor_get(v___x_1829_, 3);
v_traceState_1835_ = lean_ctor_get(v___x_1829_, 4);
v_cache_1836_ = lean_ctor_get(v___x_1829_, 5);
v_messages_1837_ = lean_ctor_get(v___x_1829_, 6);
v_snapshotTasks_1838_ = lean_ctor_get(v___x_1829_, 8);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1840_ = v___x_1829_;
v_isShared_1841_ = v_isSharedCheck_1860_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_snapshotTasks_1838_);
lean_inc(v_infoState_1830_);
lean_inc(v_messages_1837_);
lean_inc(v_cache_1836_);
lean_inc(v_traceState_1835_);
lean_inc(v_auxDeclNGen_1834_);
lean_inc(v_ngen_1833_);
lean_inc(v_nextMacroScope_1832_);
lean_inc(v_env_1831_);
lean_dec(v___x_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1860_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
uint8_t v_enabled_1842_; lean_object* v_assignment_1843_; lean_object* v_lazyAssignment_1844_; lean_object* v_trees_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1859_; 
v_enabled_1842_ = lean_ctor_get_uint8(v_infoState_1830_, sizeof(void*)*3);
v_assignment_1843_ = lean_ctor_get(v_infoState_1830_, 0);
v_lazyAssignment_1844_ = lean_ctor_get(v_infoState_1830_, 1);
v_trees_1845_ = lean_ctor_get(v_infoState_1830_, 2);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_infoState_1830_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1847_ = v_infoState_1830_;
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_trees_1845_);
lean_inc(v_lazyAssignment_1844_);
lean_inc(v_assignment_1843_);
lean_dec(v_infoState_1830_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = l_Lean_PersistentArray_push___redArg(v_trees_1845_, v_t_1821_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 2, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_assignment_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_lazyAssignment_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v___x_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*3, v_enabled_1842_);
v___x_1851_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 7, v___x_1851_);
v___x_1853_ = v___x_1840_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_env_1831_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_nextMacroScope_1832_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_ngen_1833_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_auxDeclNGen_1834_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_traceState_1835_);
lean_ctor_set(v_reuseFailAlloc_1857_, 5, v_cache_1836_);
lean_ctor_set(v_reuseFailAlloc_1857_, 6, v_messages_1837_);
lean_ctor_set(v_reuseFailAlloc_1857_, 7, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1857_, 8, v_snapshotTasks_1838_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_st_ref_put(v___y_1822_, v___x_1853_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_t_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_1861_, v___y_1862_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_unsigned_to_nat(32u);
v___x_1866_ = lean_mk_empty_array_with_capacity(v___x_1865_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1868_ = ((size_t)5ULL);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_unsigned_to_nat(32u);
v___x_1871_ = lean_mk_empty_array_with_capacity(v___x_1870_);
v___x_1872_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__0);
v___x_1873_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1871_);
lean_ctor_set(v___x_1873_, 2, v___x_1869_);
lean_ctor_set(v___x_1873_, 3, v___x_1869_);
lean_ctor_set_usize(v___x_1873_, 4, v___x_1868_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(lean_object* v_t_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v_infoState_1883_; uint8_t v_enabled_1884_; 
v___x_1882_ = lean_st_ref_get(v___y_1880_);
v_infoState_1883_ = lean_ctor_get(v___x_1882_, 7);
lean_inc_ref(v_infoState_1883_);
lean_dec(v___x_1882_);
v_enabled_1884_ = lean_ctor_get_uint8(v_infoState_1883_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1883_);
if (v_enabled_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v_t_1874_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
v___x_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_t_1874_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v___x_1888_, v___y_1880_);
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___boxed(lean_object* v_t_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v_t_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(lean_object* v_info_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_info_1899_);
v___x_1908_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3(v___x_1907_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1___boxed(lean_object* v_info_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v_info_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1917_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__13));
v___x_1957_ = l_String_toRawSubstring_x27(v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__9));
v___x_1981_ = l_String_toRawSubstring_x27(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(uint8_t v___x_1996_, lean_object* v_option_1997_, lean_object* v_fst_1998_, uint8_t v___x_1999_, lean_object* v_fst_2000_, lean_object* v_fst_2001_, lean_object* v_snd_2002_, lean_object* v_mkStructInst_2003_, lean_object* v_seenFields_2004_, lean_object* v_fields_2005_, lean_object* v_value_2006_, lean_object* v_____r_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___y_2016_; lean_object* v_source_x3f_2017_; lean_object* v_seenFields_2018_; lean_object* v_fields_2019_; lean_object* v___y_2020_; lean_object* v_value_2044_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__8));
lean_inc(v_value_2006_);
v___x_2058_ = l_Lean_Syntax_isOfKind(v_value_2006_, v___x_2057_);
if (v___x_2058_ == 0)
{
v_value_2044_ = v_value_2006_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = l_Lean_Syntax_getArg(v_value_2006_, v___x_2059_);
if (v___x_1996_ == 0)
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__10));
lean_inc(v___x_2060_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v___x_2060_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_dec(v___x_2060_);
v_value_2044_ = v_value_2006_;
goto v___jp_2043_;
}
else
{
goto v___jp_2061_;
}
}
else
{
goto v___jp_2061_;
}
v___jp_2061_:
{
lean_object* v_toCold_2062_; lean_object* v_ref_2063_; lean_object* v_currMacroScope_2064_; lean_object* v_quotContext_2065_; lean_object* v_ref_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_toCold_2062_ = lean_ctor_get(v___y_2012_, 0);
v_ref_2063_ = lean_ctor_get(v___y_2012_, 4);
v_currMacroScope_2064_ = lean_ctor_get(v___y_2012_, 9);
v_quotContext_2065_ = lean_ctor_get(v_toCold_2062_, 2);
v_ref_2066_ = l_Lean_replaceRef(v_value_2006_, v_ref_2063_);
lean_dec(v_value_2006_);
v___x_2067_ = l_Lean_SourceInfo_fromRef(v_ref_2066_, v___x_1996_);
lean_dec(v_ref_2066_);
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_2069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__14);
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__17));
lean_inc_n(v_currMacroScope_2064_, 2);
lean_inc_n(v_quotContext_2065_, 2);
v___x_2071_ = l_Lean_addMacroScope(v_quotContext_2065_, v___x_2070_, v_currMacroScope_2064_);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__20));
lean_inc_n(v___x_2067_, 7);
v___x_2073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2067_);
lean_ctor_set(v___x_2073_, 1, v___x_2069_);
lean_ctor_set(v___x_2073_, 2, v___x_2071_);
lean_ctor_set(v___x_2073_, 3, v___x_2072_);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__22));
v___x_2076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__23));
v___x_2077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2067_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__24);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__25));
v___x_2080_ = l_Lean_addMacroScope(v_quotContext_2065_, v___x_2079_, v_currMacroScope_2064_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__29));
v___x_2082_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2067_);
lean_ctor_set(v___x_2082_, 1, v___x_2078_);
lean_ctor_set(v___x_2082_, 2, v___x_2080_);
lean_ctor_set(v___x_2082_, 3, v___x_2081_);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__30));
v___x_2084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2067_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2067_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_Syntax_node5(v___x_2067_, v___x_2075_, v___x_2077_, v___x_2082_, v___x_2084_, v___x_2060_, v___x_2086_);
v___x_2088_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2074_, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2068_, v___x_2073_, v___x_2088_);
v_value_2044_ = v___x_2089_;
goto v___jp_2043_;
}
}
v___jp_2015_:
{
lean_object* v_ref_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_ref_2021_ = lean_ctor_get(v___y_2020_, 4);
v___x_2022_ = l_Lean_SourceInfo_fromRef(v_ref_2021_, v___x_1996_);
v___x_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__1));
v___x_2024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__3));
lean_inc(v_fst_1998_);
v___x_2025_ = l_Lean_mkCIdentFrom(v_option_1997_, v_fst_1998_, v___x_1999_);
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2022_, 5);
v___x_2028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2022_);
lean_ctor_set(v___x_2028_, 1, v___x_2026_);
lean_ctor_set(v___x_2028_, 2, v___x_2027_);
lean_inc_ref_n(v___x_2028_, 3);
v___x_2029_ = l_Lean_Syntax_node2(v___x_2022_, v___x_2024_, v___x_2025_, v___x_2028_);
v___x_2030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__5));
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_2032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2022_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_Syntax_node3(v___x_2022_, v___x_2030_, v___x_2032_, v___x_2028_, v___y_2016_);
v___x_2034_ = l_Lean_Syntax_node3(v___x_2022_, v___x_2026_, v___x_2028_, v___x_2028_, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_node2(v___x_2022_, v___x_2023_, v___x_2029_, v___x_2034_);
v___x_2036_ = lean_array_push(v_fields_2019_, v___x_2035_);
v___x_2037_ = l_Lean_NameSet_insert(v_seenFields_2018_, v_fst_1998_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2036_);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_source_x3f_2017_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
v___jp_2043_:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_NameSet_contains(v_fst_2000_, v_fst_1998_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v_fields_2005_);
lean_dec(v_seenFields_2004_);
lean_dec_ref(v_mkStructInst_2003_);
v___y_2016_ = v_value_2044_;
v_source_x3f_2017_ = v_fst_2001_;
v_seenFields_2018_ = v_fst_2000_;
v_fields_2019_ = v_snd_2002_;
v___y_2020_ = v___y_2012_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2046_; 
lean_dec(v_fst_2000_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
v___x_2046_ = lean_apply_9(v_mkStructInst_2003_, v_fst_2001_, v_snd_2002_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, lean_box(0));
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_a_2047_);
v___y_2016_ = v_value_2044_;
v_source_x3f_2017_ = v___x_2048_;
v_seenFields_2018_ = v_seenFields_2004_;
v_fields_2019_ = v_fields_2005_;
v___y_2020_ = v___y_2012_;
goto v___jp_2015_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_value_2044_);
lean_dec_ref(v_fields_2005_);
lean_dec(v_seenFields_2004_);
lean_dec(v_fst_1998_);
v_a_2049_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2046_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2046_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v___x_2092_ = _args[0];
lean_object* v_option_2093_ = _args[1];
lean_object* v_fst_2094_ = _args[2];
lean_object* v___x_2095_ = _args[3];
lean_object* v_fst_2096_ = _args[4];
lean_object* v_fst_2097_ = _args[5];
lean_object* v_snd_2098_ = _args[6];
lean_object* v_mkStructInst_2099_ = _args[7];
lean_object* v_seenFields_2100_ = _args[8];
lean_object* v_fields_2101_ = _args[9];
lean_object* v_value_2102_ = _args[10];
lean_object* v_____r_2103_ = _args[11];
lean_object* v___y_2104_ = _args[12];
lean_object* v___y_2105_ = _args[13];
lean_object* v___y_2106_ = _args[14];
lean_object* v___y_2107_ = _args[15];
lean_object* v___y_2108_ = _args[16];
lean_object* v___y_2109_ = _args[17];
lean_object* v___y_2110_ = _args[18];
_start:
{
uint8_t v___x_50884__boxed_2111_; uint8_t v___x_50886__boxed_2112_; lean_object* v_res_2113_; 
v___x_50884__boxed_2111_ = lean_unbox(v___x_2092_);
v___x_50886__boxed_2112_ = lean_unbox(v___x_2095_);
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_50884__boxed_2111_, v_option_2093_, v_fst_2094_, v___x_50886__boxed_2112_, v_fst_2096_, v_fst_2097_, v_snd_2098_, v_mkStructInst_2099_, v_seenFields_2100_, v_fields_2101_, v_value_2102_, v_____r_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v_option_2093_);
return v_res_2113_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2116_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__1);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = lean_box(1);
v___x_2120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__2);
v___x_2122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2120_);
lean_ctor_set(v___x_2122_, 2, v___x_2119_);
return v___x_2122_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_box(0);
v___x_2126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__4));
v___x_2127_ = l_Lean_Expr_const___override(v___x_2126_, v___x_2125_);
return v___x_2127_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__6));
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__8));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(lean_object* v_structName_2134_, uint8_t v_recover_2135_, lean_object* v_as_2136_, size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_fst_2148_; lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec(v_structName_2134_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_b_2139_);
return v___x_2158_;
}
else
{
lean_object* v_snd_2159_; lean_object* v_fst_2160_; lean_object* v_fst_2161_; lean_object* v_snd_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2274_; 
v_snd_2159_ = lean_ctor_get(v_b_2139_, 1);
lean_inc(v_snd_2159_);
v_fst_2160_ = lean_ctor_get(v_b_2139_, 0);
lean_inc(v_fst_2160_);
lean_dec_ref(v_b_2139_);
v_fst_2161_ = lean_ctor_get(v_snd_2159_, 0);
v_snd_2162_ = lean_ctor_get(v_snd_2159_, 1);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_snd_2159_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2164_ = v_snd_2159_;
v_isShared_2165_ = v_isSharedCheck_2274_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_snd_2162_);
lean_inc(v_fst_2161_);
lean_dec(v_snd_2159_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2274_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___y_2167_; uint8_t v___y_2168_; lean_object* v_a_2181_; lean_object* v___y_2185_; lean_object* v_a_2193_; lean_object* v_ref_2194_; lean_object* v_option_2195_; lean_object* v_value_2196_; uint8_t v_bool_2197_; lean_object* v_mkStructInst_2198_; lean_object* v_seenFields_2199_; lean_object* v_fields_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_a_2193_ = lean_array_uget_borrowed(v_as_2136_, v_i_2138_);
v_ref_2194_ = lean_ctor_get(v_a_2193_, 0);
v_option_2195_ = lean_ctor_get(v_a_2193_, 1);
v_value_2196_ = lean_ctor_get(v_a_2193_, 2);
v_bool_2197_ = lean_ctor_get_uint8(v_a_2193_, sizeof(void*)*3);
lean_inc(v_structName_2134_);
v_mkStructInst_2198_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___boxed), 10, 1);
lean_closure_set(v_mkStructInst_2198_, 0, v_structName_2134_);
v_seenFields_2199_ = l_Lean_NameSet_empty;
v_fields_2200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v___x_2201_ = l_Lean_TSyntax_getId(v_option_2195_);
v___x_2202_ = l_Lean_Name_eraseMacroScopes(v___x_2201_);
lean_dec(v___x_2201_);
v___x_2203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__7));
v___x_2204_ = lean_name_eq(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3);
lean_inc(v___x_2202_);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2202_);
lean_inc(v_structName_2134_);
lean_inc(v_option_2195_);
v___x_2207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2207_, 0, v_option_2195_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_ctor_set(v___x_2207_, 2, v___x_2205_);
lean_ctor_set(v___x_2207_, 3, v_structName_2134_);
v___x_2208_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1(v___x_2207_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_toCold_2209_; lean_object* v_options_2210_; lean_object* v_currRecDepth_2211_; lean_object* v_maxRecDepth_2212_; lean_object* v_ref_2213_; lean_object* v_currNamespace_2214_; lean_object* v_openDecls_2215_; lean_object* v_initHeartbeats_2216_; lean_object* v_maxHeartbeats_2217_; lean_object* v_currMacroScope_2218_; uint8_t v_diag_2219_; uint8_t v_suppressElabErrors_2220_; lean_object* v_ref_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref_known(v___x_2208_, 1);
v_toCold_2209_ = lean_ctor_get(v___y_2144_, 0);
v_options_2210_ = lean_ctor_get(v___y_2144_, 1);
v_currRecDepth_2211_ = lean_ctor_get(v___y_2144_, 2);
v_maxRecDepth_2212_ = lean_ctor_get(v___y_2144_, 3);
v_ref_2213_ = lean_ctor_get(v___y_2144_, 4);
v_currNamespace_2214_ = lean_ctor_get(v___y_2144_, 5);
v_openDecls_2215_ = lean_ctor_get(v___y_2144_, 6);
v_initHeartbeats_2216_ = lean_ctor_get(v___y_2144_, 7);
v_maxHeartbeats_2217_ = lean_ctor_get(v___y_2144_, 8);
v_currMacroScope_2218_ = lean_ctor_get(v___y_2144_, 9);
v_diag_2219_ = lean_ctor_get_uint8(v___y_2144_, sizeof(void*)*10);
v_suppressElabErrors_2220_ = lean_ctor_get_uint8(v___y_2144_, sizeof(void*)*10 + 1);
v_ref_2221_ = l_Lean_replaceRef(v_option_2195_, v_ref_2213_);
lean_inc(v_currMacroScope_2218_);
lean_inc(v_maxHeartbeats_2217_);
lean_inc(v_initHeartbeats_2216_);
lean_inc(v_openDecls_2215_);
lean_inc(v_currNamespace_2214_);
lean_inc(v_maxRecDepth_2212_);
lean_inc(v_currRecDepth_2211_);
lean_inc_ref(v_options_2210_);
lean_inc_ref(v_toCold_2209_);
v___x_2222_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2222_, 0, v_toCold_2209_);
lean_ctor_set(v___x_2222_, 1, v_options_2210_);
lean_ctor_set(v___x_2222_, 2, v_currRecDepth_2211_);
lean_ctor_set(v___x_2222_, 3, v_maxRecDepth_2212_);
lean_ctor_set(v___x_2222_, 4, v_ref_2221_);
lean_ctor_set(v___x_2222_, 5, v_currNamespace_2214_);
lean_ctor_set(v___x_2222_, 6, v_openDecls_2215_);
lean_ctor_set(v___x_2222_, 7, v_initHeartbeats_2216_);
lean_ctor_set(v___x_2222_, 8, v_maxHeartbeats_2217_);
lean_ctor_set(v___x_2222_, 9, v_currMacroScope_2218_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*10, v_diag_2219_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*10 + 1, v_suppressElabErrors_2220_);
lean_inc(v___x_2202_);
lean_inc(v_structName_2134_);
v___x_2223_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandField(v_structName_2134_, v___x_2202_, v___y_2142_, v___y_2143_, v___x_2222_, v___y_2145_);
lean_dec_ref_known(v___x_2222_, 10);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
if (v_bool_2197_ == 0)
{
lean_object* v_fst_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v___x_2202_);
lean_del_object(v___x_2164_);
v_fst_2225_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_fst_2225_);
lean_dec(v_a_2224_);
v___x_2226_ = lean_box(0);
lean_inc(v_value_2196_);
lean_inc(v_snd_2162_);
lean_inc(v_fst_2160_);
lean_inc(v_fst_2161_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2204_, v_option_2195_, v_fst_2225_, v___x_2157_, v_fst_2161_, v_fst_2160_, v_snd_2162_, v_mkStructInst_2198_, v_seenFields_2199_, v_fields_2200_, v_value_2196_, v___x_2226_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v___y_2185_ = v___x_2227_;
goto v___jp_2184_;
}
else
{
lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2255_; 
v_fst_2228_ = lean_ctor_get(v_a_2224_, 0);
v_snd_2229_ = lean_ctor_get(v_a_2224_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_a_2224_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2231_ = v_a_2224_;
v_isShared_2232_ = v_isSharedCheck_2255_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_snd_2229_);
lean_inc(v_fst_2228_);
lean_dec(v_a_2224_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2255_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2(v_snd_2229_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_Lean_ConstantInfo_type(v_a_2234_);
lean_dec(v_a_2234_);
v___x_2236_ = l_Lean_Expr_bindingBody_x21(v___x_2235_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__5);
v___x_2238_ = lean_expr_eqv(v___x_2236_, v___x_2237_);
lean_dec_ref(v___x_2236_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__7);
v___x_2240_ = l_Lean_MessageData_ofName(v___x_2202_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 7);
lean_ctor_set(v___x_2231_, 1, v___x_2240_);
lean_ctor_set(v___x_2231_, 0, v___x_2239_);
v___x_2242_ = v___x_2231_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__9);
if (v_isShared_2165_ == 0)
{
lean_ctor_set_tag(v___x_2164_, 7);
lean_ctor_set(v___x_2164_, 1, v___x_2243_);
lean_ctor_set(v___x_2164_, 0, v___x_2242_);
v___x_2245_ = v___x_2164_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_2194_, v___x_2245_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
lean_inc(v_value_2196_);
lean_inc(v_snd_2162_);
lean_inc(v_fst_2160_);
lean_inc(v_fst_2161_);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2204_, v_option_2195_, v_fst_2228_, v___x_2157_, v_fst_2161_, v_fst_2160_, v_snd_2162_, v_mkStructInst_2198_, v_seenFields_2199_, v_fields_2200_, v_value_2196_, v_a_2247_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v___y_2185_ = v___x_2248_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2249_; 
lean_dec(v_fst_2228_);
lean_dec_ref(v_mkStructInst_2198_);
v_a_2249_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2246_, 1);
v_a_2181_ = v_a_2249_;
goto v___jp_2180_;
}
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_del_object(v___x_2231_);
lean_dec(v___x_2202_);
lean_del_object(v___x_2164_);
v___x_2252_ = lean_box(0);
lean_inc(v_value_2196_);
lean_inc(v_snd_2162_);
lean_inc(v_fst_2160_);
lean_inc(v_fst_2161_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1(v___x_2204_, v_option_2195_, v_fst_2228_, v___x_2157_, v_fst_2161_, v_fst_2160_, v_snd_2162_, v_mkStructInst_2198_, v_seenFields_2199_, v_fields_2200_, v_value_2196_, v___x_2252_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v___y_2185_ = v___x_2253_;
goto v___jp_2184_;
}
}
else
{
lean_object* v_a_2254_; 
lean_del_object(v___x_2231_);
lean_dec(v_fst_2228_);
lean_dec(v___x_2202_);
lean_dec_ref(v_mkStructInst_2198_);
lean_del_object(v___x_2164_);
v_a_2254_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2233_, 1);
v_a_2181_ = v_a_2254_;
goto v___jp_2180_;
}
}
}
}
else
{
lean_object* v_a_2256_; 
lean_dec(v___x_2202_);
lean_dec_ref(v_mkStructInst_2198_);
lean_del_object(v___x_2164_);
v_a_2256_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2223_, 1);
v_a_2181_ = v_a_2256_;
goto v___jp_2180_;
}
}
else
{
lean_object* v_a_2257_; 
lean_dec(v___x_2202_);
lean_dec_ref(v_mkStructInst_2198_);
lean_del_object(v___x_2164_);
v_a_2257_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2208_, 1);
v_a_2181_ = v_a_2257_;
goto v___jp_2180_;
}
}
else
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
lean_dec(v___x_2202_);
lean_dec_ref(v_mkStructInst_2198_);
lean_del_object(v___x_2164_);
v___x_2258_ = lean_array_get_size(v_snd_2162_);
v___x_2259_ = lean_nat_dec_eq(v___x_2258_, v___x_2156_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_inc(v_fst_2160_);
lean_inc(v_structName_2134_);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0(v_structName_2134_, v_fst_2160_, v_snd_2162_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2270_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2270_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2270_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set_tag(v___x_2263_, 1);
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_box(0);
lean_inc(v_structName_2134_);
lean_inc(v_a_2193_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2193_, v_structName_2134_, v___x_2267_, v___x_2266_, v_seenFields_2199_, v_fields_2200_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v___y_2185_ = v___x_2268_;
goto v___jp_2184_;
}
}
}
else
{
lean_object* v_a_2271_; 
v_a_2271_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2260_, 1);
v_a_2181_ = v_a_2271_;
goto v___jp_2180_;
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_box(0);
lean_inc(v_snd_2162_);
lean_inc(v_fst_2161_);
lean_inc(v_fst_2160_);
lean_inc(v_structName_2134_);
lean_inc(v_a_2193_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2(v_a_2193_, v_structName_2134_, v___x_2272_, v_fst_2160_, v_fst_2161_, v_snd_2162_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v___y_2185_ = v___x_2273_;
goto v___jp_2184_;
}
}
v___jp_2166_:
{
if (v___y_2168_ == 0)
{
if (v_recover_2135_ == 0)
{
lean_object* v___x_2169_; 
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
lean_dec(v_fst_2160_);
lean_dec(v_structName_2134_);
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___y_2167_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0(v___y_2167_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_dec_ref_known(v___x_2170_, 1);
v_fst_2148_ = v_fst_2160_;
v_fst_2149_ = v_fst_2161_;
v_snd_2150_ = v_snd_2162_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
lean_dec(v_fst_2160_);
lean_dec(v_structName_2134_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v___x_2179_; 
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
lean_dec(v_fst_2160_);
lean_dec(v_structName_2134_);
v___x_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___y_2167_);
return v___x_2179_;
}
}
v___jp_2180_:
{
uint8_t v___x_2182_; 
v___x_2182_ = l_Lean_Exception_isInterrupt(v_a_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
lean_inc_ref(v_a_2181_);
v___x_2183_ = l_Lean_Exception_isRuntime(v_a_2181_);
v___y_2167_ = v_a_2181_;
v___y_2168_ = v___x_2183_;
goto v___jp_2166_;
}
else
{
v___y_2167_ = v_a_2181_;
v___y_2168_ = v___x_2182_;
goto v___jp_2166_;
}
}
v___jp_2184_:
{
if (lean_obj_tag(v___y_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v_snd_2187_; lean_object* v_snd_2188_; lean_object* v_fst_2189_; lean_object* v_fst_2190_; lean_object* v_snd_2191_; 
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
lean_dec(v_fst_2160_);
v_a_2186_ = lean_ctor_get(v___y_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___y_2185_, 1);
v_snd_2187_ = lean_ctor_get(v_a_2186_, 1);
lean_inc(v_snd_2187_);
lean_dec(v_a_2186_);
v_snd_2188_ = lean_ctor_get(v_snd_2187_, 1);
lean_inc(v_snd_2188_);
v_fst_2189_ = lean_ctor_get(v_snd_2187_, 0);
lean_inc(v_fst_2189_);
lean_dec(v_snd_2187_);
v_fst_2190_ = lean_ctor_get(v_snd_2188_, 0);
lean_inc(v_fst_2190_);
v_snd_2191_ = lean_ctor_get(v_snd_2188_, 1);
lean_inc(v_snd_2191_);
lean_dec(v_snd_2188_);
v_fst_2148_ = v_fst_2189_;
v_fst_2149_ = v_fst_2190_;
v_snd_2150_ = v_snd_2191_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2192_; 
v_a_2192_ = lean_ctor_get(v___y_2185_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___y_2185_, 1);
v_a_2181_ = v_a_2192_;
goto v___jp_2180_;
}
}
}
}
v___jp_2147_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; size_t v___x_2153_; size_t v___x_2154_; 
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_fst_2149_);
lean_ctor_set(v___x_2151_, 1, v_snd_2150_);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_fst_2148_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_add(v_i_2138_, v___x_2153_);
v_i_2138_ = v___x_2154_;
v_b_2139_ = v___x_2152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___boxed(lean_object* v_structName_2275_, lean_object* v_recover_2276_, lean_object* v_as_2277_, lean_object* v_sz_2278_, lean_object* v_i_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_recover_boxed_2288_; size_t v_sz_boxed_2289_; size_t v_i_boxed_2290_; lean_object* v_res_2291_; 
v_recover_boxed_2288_ = lean_unbox(v_recover_2276_);
v_sz_boxed_2289_ = lean_unbox_usize(v_sz_2278_);
lean_dec(v_sz_2278_);
v_i_boxed_2290_ = lean_unbox_usize(v_i_2279_);
lean_dec(v_i_2279_);
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2275_, v_recover_boxed_2288_, v_as_2277_, v_sz_boxed_2289_, v_i_boxed_2290_, v_b_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_as_2277_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0(lean_object* v_structName_2292_, uint8_t v_recover_2293_, lean_object* v_items_2294_, size_t v_sz_2295_, size_t v___x_2296_, lean_object* v___x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_a_2306_; lean_object* v___x_2319_; 
lean_inc(v_structName_2292_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4(v_structName_2292_, v_recover_2293_, v_items_2294_, v_sz_2295_, v___x_2296_, v___x_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v_snd_2321_; lean_object* v_fst_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2399_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v_snd_2321_ = lean_ctor_get(v_a_2320_, 1);
v_fst_2322_ = lean_ctor_get(v_a_2320_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_a_2320_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2324_ = v_a_2320_;
v_isShared_2325_ = v_isSharedCheck_2399_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snd_2321_);
lean_inc(v_fst_2322_);
lean_dec(v_a_2320_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2399_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
if (lean_obj_tag(v_fst_2322_) == 0)
{
lean_object* v_snd_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2358_; 
v_snd_2326_ = lean_ctor_get(v_snd_2321_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_snd_2321_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v_snd_2321_, 0);
lean_dec(v_unused_2359_);
v___x_2328_ = v_snd_2321_;
v_isShared_2329_ = v_isSharedCheck_2358_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snd_2326_);
lean_dec(v_snd_2321_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2358_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_ref_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v_ref_2330_ = lean_ctor_get(v___y_2302_, 4);
v___x_2331_ = 0;
v___x_2332_ = l_Lean_SourceInfo_fromRef(v_ref_2330_, v___x_2331_);
v___x_2333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2332_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 2);
lean_ctor_set(v___x_2328_, 1, v___x_2334_);
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2336_ = v___x_2328_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_2338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
lean_inc_n(v___x_2332_, 5);
v___x_2339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2332_);
lean_ctor_set(v___x_2339_, 1, v___x_2337_);
lean_ctor_set(v___x_2339_, 2, v___x_2338_);
v___x_2340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2342_ = l_Lean_Syntax_SepArray_ofElems(v___x_2341_, v_snd_2326_);
lean_dec(v_snd_2326_);
v___x_2343_ = l_Array_append___redArg(v___x_2338_, v___x_2342_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2332_);
lean_ctor_set(v___x_2344_, 1, v___x_2337_);
lean_ctor_set(v___x_2344_, 2, v___x_2343_);
v___x_2345_ = l_Lean_Syntax_node1(v___x_2332_, v___x_2340_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
lean_inc_ref(v___x_2339_);
v___x_2347_ = l_Lean_Syntax_node1(v___x_2332_, v___x_2346_, v___x_2339_);
v___x_2348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
if (v_isShared_2325_ == 0)
{
lean_ctor_set_tag(v___x_2324_, 2);
lean_ctor_set(v___x_2324_, 1, v___x_2348_);
lean_ctor_set(v___x_2324_, 0, v___x_2332_);
v___x_2350_ = v___x_2324_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_inc(v_structName_2292_);
v___x_2351_ = l_Lean_mkCIdent(v_structName_2292_);
lean_inc_n(v___x_2332_, 2);
v___x_2352_ = l_Lean_Syntax_node2(v___x_2332_, v___x_2337_, v___x_2350_, v___x_2351_);
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2332_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = l_Lean_Syntax_node6(v___x_2332_, v___x_2333_, v___x_2336_, v___x_2339_, v___x_2345_, v___x_2347_, v___x_2352_, v___x_2354_);
v_a_2306_ = v___x_2355_;
goto v___jp_2305_;
}
}
}
}
else
{
lean_object* v_snd_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2397_; 
v_snd_2360_ = lean_ctor_get(v_snd_2321_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_snd_2321_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v_snd_2321_, 0);
lean_dec(v_unused_2398_);
v___x_2362_ = v_snd_2321_;
v_isShared_2363_ = v_isSharedCheck_2397_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_snd_2360_);
lean_dec(v_snd_2321_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2397_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_val_2364_; lean_object* v_ref_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v_val_2364_ = lean_ctor_get(v_fst_2322_, 0);
lean_inc(v_val_2364_);
lean_dec_ref_known(v_fst_2322_, 1);
v_ref_2365_ = lean_ctor_get(v___y_2302_, 4);
v___x_2366_ = 0;
v___x_2367_ = l_Lean_SourceInfo_fromRef(v_ref_2365_, v___x_2366_);
v___x_2368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_2369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc(v___x_2367_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 2);
lean_ctor_set(v___x_2362_, 1, v___x_2369_);
lean_ctor_set(v___x_2362_, 0, v___x_2367_);
v___x_2371_ = v___x_2362_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
lean_inc_n(v___x_2367_, 2);
v___x_2373_ = l_Lean_Syntax_node1(v___x_2367_, v___x_2372_, v_val_2364_);
v___x_2374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__14));
if (v_isShared_2325_ == 0)
{
lean_ctor_set_tag(v___x_2324_, 2);
lean_ctor_set(v___x_2324_, 1, v___x_2374_);
lean_ctor_set(v___x_2324_, 0, v___x_2367_);
v___x_2376_ = v___x_2324_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_inc_n(v___x_2367_, 8);
v___x_2377_ = l_Lean_Syntax_node2(v___x_2367_, v___x_2372_, v___x_2373_, v___x_2376_);
v___x_2378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
v___x_2379_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_2380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__9));
v___x_2381_ = l_Lean_Syntax_SepArray_ofElems(v___x_2380_, v_snd_2360_);
lean_dec(v_snd_2360_);
v___x_2382_ = l_Array_append___redArg(v___x_2379_, v___x_2381_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2367_);
lean_ctor_set(v___x_2383_, 1, v___x_2372_);
lean_ctor_set(v___x_2383_, 2, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node1(v___x_2367_, v___x_2378_, v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_2386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2367_);
lean_ctor_set(v___x_2386_, 1, v___x_2372_);
lean_ctor_set(v___x_2386_, 2, v___x_2379_);
v___x_2387_ = l_Lean_Syntax_node1(v___x_2367_, v___x_2385_, v___x_2386_);
v___x_2388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_2389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2367_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v_structName_2292_);
v___x_2390_ = l_Lean_mkCIdent(v_structName_2292_);
v___x_2391_ = l_Lean_Syntax_node2(v___x_2367_, v___x_2372_, v___x_2389_, v___x_2390_);
v___x_2392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_2393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2367_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Lean_Syntax_node6(v___x_2367_, v___x_2368_, v___x_2371_, v___x_2377_, v___x_2384_, v___x_2387_, v___x_2391_, v___x_2393_);
v_a_2306_ = v___x_2394_;
goto v___jp_2305_;
}
}
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_structName_2292_);
v_a_2400_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2319_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2319_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
v___jp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = l_Lean_mkConst(v_structName_2292_, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
v___x_2310_ = 1;
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_box(v___x_2310_);
v___x_2313_ = lean_box(v___x_2310_);
v___x_2314_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2314_, 0, v_a_2306_);
lean_closure_set(v___x_2314_, 1, v___x_2309_);
lean_closure_set(v___x_2314_, 2, v___x_2312_);
lean_closure_set(v___x_2314_, 3, v___x_2313_);
lean_closure_set(v___x_2314_, 4, v___x_2311_);
v___x_2315_ = 1;
v___x_2316_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2314_, v___x_2315_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabConfig_spec__5___redArg(v_a_2317_, v___y_2301_);
return v___x_2318_;
}
else
{
return v___x_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___lam__0___boxed(lean_object* v_structName_2408_, lean_object* v_recover_2409_, lean_object* v_items_2410_, lean_object* v_sz_2411_, lean_object* v___x_2412_, lean_object* v___x_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v_recover_boxed_2421_; size_t v_sz_boxed_2422_; size_t v___x_51471__boxed_2423_; lean_object* v_res_2424_; 
v_recover_boxed_2421_ = lean_unbox(v_recover_2409_);
v_sz_boxed_2422_ = lean_unbox_usize(v_sz_2411_);
lean_dec(v_sz_2411_);
v___x_51471__boxed_2423_ = lean_unbox_usize(v___x_2412_);
lean_dec(v___x_2412_);
v_res_2424_ = l_Lean_Elab_Tactic_elabConfig___lam__0(v_structName_2408_, v_recover_boxed_2421_, v_items_2410_, v_sz_boxed_2422_, v___x_51471__boxed_2423_, v___x_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec_ref(v_items_2410_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v_env_2430_; lean_object* v___x_2431_; lean_object* v_mctx_2432_; lean_object* v_options_2433_; lean_object* v_currNamespace_2434_; lean_object* v_openDecls_2435_; lean_object* v___x_2436_; lean_object* v_ngen_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2429_ = lean_st_ref_get(v___y_2427_);
v_env_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_ref(v_env_2430_);
lean_dec(v___x_2429_);
v___x_2431_ = lean_st_ref_get(v___y_2425_);
v_mctx_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc_ref(v_mctx_2432_);
lean_dec(v___x_2431_);
v_options_2433_ = lean_ctor_get(v___y_2426_, 1);
v_currNamespace_2434_ = lean_ctor_get(v___y_2426_, 5);
v_openDecls_2435_ = lean_ctor_get(v___y_2426_, 6);
v___x_2436_ = lean_st_ref_get(v___y_2427_);
v_ngen_2437_ = lean_ctor_get(v___x_2436_, 2);
lean_inc_ref(v_ngen_2437_);
lean_dec(v___x_2436_);
v___x_2438_ = lean_box(0);
v___x_2439_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_2435_);
lean_inc(v_currNamespace_2434_);
lean_inc_ref(v_options_2433_);
v___x_2440_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2440_, 0, v_env_2430_);
lean_ctor_set(v___x_2440_, 1, v___x_2438_);
lean_ctor_set(v___x_2440_, 2, v___x_2439_);
lean_ctor_set(v___x_2440_, 3, v_mctx_2432_);
lean_ctor_set(v___x_2440_, 4, v_options_2433_);
lean_ctor_set(v___x_2440_, 5, v_currNamespace_2434_);
lean_ctor_set(v___x_2440_, 6, v_openDecls_2435_);
lean_ctor_set(v___x_2440_, 7, v_ngen_2437_);
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; lean_object* v_toCold_2455_; lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2480_; 
v___x_2454_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_2450_, v___y_2451_, v___y_2452_);
v_toCold_2455_ = lean_ctor_get(v___y_2451_, 0);
v_a_2456_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2458_ = v___x_2454_;
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_fileMap_2460_; lean_object* v_env_2461_; lean_object* v_mctx_2462_; lean_object* v_options_2463_; lean_object* v_currNamespace_2464_; lean_object* v_openDecls_2465_; lean_object* v_ngen_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2477_; 
v_fileMap_2460_ = lean_ctor_get(v_toCold_2455_, 1);
v_env_2461_ = lean_ctor_get(v_a_2456_, 0);
v_mctx_2462_ = lean_ctor_get(v_a_2456_, 3);
v_options_2463_ = lean_ctor_get(v_a_2456_, 4);
v_currNamespace_2464_ = lean_ctor_get(v_a_2456_, 5);
v_openDecls_2465_ = lean_ctor_get(v_a_2456_, 6);
v_ngen_2466_ = lean_ctor_get(v_a_2456_, 7);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_a_2456_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; lean_object* v_unused_2479_; 
v_unused_2478_ = lean_ctor_get(v_a_2456_, 2);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_a_2456_, 1);
lean_dec(v_unused_2479_);
v___x_2468_ = v_a_2456_;
v_isShared_2469_ = v_isSharedCheck_2477_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_ngen_2466_);
lean_inc(v_openDecls_2465_);
lean_inc(v_currNamespace_2464_);
lean_inc(v_options_2463_);
lean_inc(v_mctx_2462_);
lean_inc(v_env_2461_);
lean_dec(v_a_2456_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2477_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2470_ = lean_box(0);
lean_inc_ref(v_fileMap_2460_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 2, v_fileMap_2460_);
lean_ctor_set(v___x_2468_, 1, v___x_2470_);
v___x_2472_ = v___x_2468_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_env_2461_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_fileMap_2460_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_mctx_2462_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_options_2463_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v_currNamespace_2464_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_openDecls_2465_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_ngen_2466_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2472_);
v___x_2474_ = v___x_2458_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11___boxed(lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2506_; 
v___x_2496_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11(v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2506_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2506_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2497_);
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2502_);
v___x_2504_ = v___x_2499_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0___boxed(lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___lam__0(v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(lean_object* v___x_2515_, lean_object* v_ctx_x3f_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref(v_ctx_x3f_2516_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_bs_2519_);
return v___x_2528_;
}
else
{
lean_object* v_assignment_2529_; lean_object* v___x_2530_; 
v_assignment_2529_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_ctx_x3f_2516_);
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
v___x_2530_ = lean_apply_7(v_ctx_x3f_2516_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, lean_box(0));
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_v_2532_; lean_object* v___x_2533_; lean_object* v_bs_x27_2534_; lean_object* v_a_2536_; lean_object* v_tree_2541_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v_v_2532_ = lean_array_uget(v_bs_2519_, v_i_2518_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v_bs_x27_2534_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2533_);
v_tree_2541_ = l_Lean_Elab_InfoTree_substitute(v_v_2532_, v_assignment_2529_);
if (lean_obj_tag(v_a_2531_) == 0)
{
v_a_2536_ = v_tree_2541_;
goto v___jp_2535_;
}
else
{
lean_object* v_val_2542_; lean_object* v___x_2543_; 
v_val_2542_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_val_2542_);
lean_dec_ref_known(v_a_2531_, 1);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_val_2542_);
lean_ctor_set(v___x_2543_, 1, v_tree_2541_);
v_a_2536_ = v___x_2543_;
goto v___jp_2535_;
}
v___jp_2535_:
{
size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2518_, v___x_2537_);
v___x_2539_ = lean_array_uset(v_bs_x27_2534_, v_i_2518_, v_a_2536_);
v_i_2518_ = v___x_2538_;
v_bs_2519_ = v___x_2539_;
goto _start;
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_bs_2519_);
lean_dec_ref(v_ctx_x3f_2516_);
v_a_2544_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2530_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2530_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27___boxed(lean_object* v___x_2552_, lean_object* v_ctx_x3f_2553_, lean_object* v_sz_2554_, lean_object* v_i_2555_, lean_object* v_bs_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
size_t v_sz_boxed_2564_; size_t v_i_boxed_2565_; lean_object* v_res_2566_; 
v_sz_boxed_2564_ = lean_unbox_usize(v_sz_2554_);
lean_dec(v_sz_2554_);
v_i_boxed_2565_ = lean_unbox_usize(v_i_2555_);
lean_dec(v_i_2555_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2552_, v_ctx_x3f_2553_, v_sz_boxed_2564_, v_i_boxed_2565_, v_bs_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___x_2552_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(lean_object* v___x_2567_, lean_object* v_ctx_x3f_2568_, lean_object* v_x_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
if (lean_obj_tag(v_x_2569_) == 0)
{
lean_object* v_cs_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2603_; 
v_cs_2577_ = lean_ctor_get(v_x_2569_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_x_2569_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2579_ = v_x_2569_;
v_isShared_2580_ = v_isSharedCheck_2603_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_cs_2577_);
lean_dec(v_x_2569_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2603_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v_sz_2581_ = lean_array_size(v_cs_2577_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2567_, v_ctx_x3f_2568_, v_sz_2581_, v___x_2582_, v_cs_2577_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2594_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2594_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2594_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_a_2584_);
v___x_2589_ = v___x_2579_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2589_);
v___x_2591_ = v___x_2586_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_del_object(v___x_2579_);
v_a_2595_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2583_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2583_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
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
}
else
{
lean_object* v_vs_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2630_; 
v_vs_2604_ = lean_ctor_get(v_x_2569_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_x_2569_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2606_ = v_x_2569_;
v_isShared_2607_ = v_isSharedCheck_2630_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_vs_2604_);
lean_dec(v_x_2569_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2630_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
size_t v_sz_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
v_sz_2608_ = lean_array_size(v_vs_2604_);
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2567_, v_ctx_x3f_2568_, v_sz_2608_, v___x_2609_, v_vs_2604_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2621_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2621_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2621_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_a_2611_);
v___x_2616_ = v___x_2606_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2618_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2616_);
v___x_2618_ = v___x_2613_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_del_object(v___x_2606_);
v_a_2622_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2610_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2610_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(lean_object* v___x_2631_, lean_object* v_ctx_x3f_2632_, size_t v_sz_2633_, size_t v_i_2634_, lean_object* v_bs_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_usize_dec_lt(v_i_2634_, v_sz_2633_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_dec_ref(v_ctx_x3f_2632_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_bs_2635_);
return v___x_2644_;
}
else
{
lean_object* v_v_2645_; lean_object* v___x_2646_; 
v_v_2645_ = lean_array_uget_borrowed(v_bs_2635_, v_i_2634_);
lean_inc(v_v_2645_);
lean_inc_ref(v_ctx_x3f_2632_);
v___x_2646_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2631_, v_ctx_x3f_2632_, v_v_2645_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v_bs_x27_2649_; size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = lean_unsigned_to_nat(0u);
v_bs_x27_2649_ = lean_array_uset(v_bs_2635_, v_i_2634_, v___x_2648_);
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_add(v_i_2634_, v___x_2650_);
v___x_2652_ = lean_array_uset(v_bs_x27_2649_, v_i_2634_, v_a_2647_);
v_i_2634_ = v___x_2651_;
v_bs_2635_ = v___x_2652_;
goto _start;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_bs_2635_);
lean_dec_ref(v_ctx_x3f_2632_);
v_a_2654_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2646_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2646_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28___boxed(lean_object* v___x_2662_, lean_object* v_ctx_x3f_2663_, lean_object* v_sz_2664_, lean_object* v_i_2665_, lean_object* v_bs_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
size_t v_sz_boxed_2674_; size_t v_i_boxed_2675_; lean_object* v_res_2676_; 
v_sz_boxed_2674_ = lean_unbox_usize(v_sz_2664_);
lean_dec(v_sz_2664_);
v_i_boxed_2675_ = lean_unbox_usize(v_i_2665_);
lean_dec(v_i_2665_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26_spec__28(v___x_2662_, v_ctx_x3f_2663_, v_sz_boxed_2674_, v_i_boxed_2675_, v_bs_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec_ref(v___x_2662_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26___boxed(lean_object* v___x_2677_, lean_object* v_ctx_x3f_2678_, lean_object* v_x_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2677_, v_ctx_x3f_2678_, v_x_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v___x_2677_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(lean_object* v___x_2688_, lean_object* v_ctx_x3f_2689_, lean_object* v_t_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_root_2698_; lean_object* v_tail_2699_; lean_object* v_size_2700_; size_t v_shift_2701_; lean_object* v_tailOff_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2738_; 
v_root_2698_ = lean_ctor_get(v_t_2690_, 0);
v_tail_2699_ = lean_ctor_get(v_t_2690_, 1);
v_size_2700_ = lean_ctor_get(v_t_2690_, 2);
v_shift_2701_ = lean_ctor_get_usize(v_t_2690_, 4);
v_tailOff_2702_ = lean_ctor_get(v_t_2690_, 3);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_t_2690_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2704_ = v_t_2690_;
v_isShared_2705_ = v_isSharedCheck_2738_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_tailOff_2702_);
lean_inc(v_size_2700_);
lean_inc(v_tail_2699_);
lean_inc(v_root_2698_);
lean_dec(v_t_2690_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2738_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; 
lean_inc_ref(v_ctx_x3f_2689_);
v___x_2706_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__26(v___x_2688_, v_ctx_x3f_2689_, v_root_2698_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; size_t v_sz_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
v_sz_2708_ = lean_array_size(v_tail_2699_);
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22_spec__27(v___x_2688_, v_ctx_x3f_2689_, v_sz_2708_, v___x_2709_, v_tail_2699_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2721_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2721_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2721_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v_a_2711_);
lean_ctor_set(v___x_2704_, 0, v_a_2707_);
v___x_2716_ = v___x_2704_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2707_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_a_2711_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_size_2700_);
lean_ctor_set(v_reuseFailAlloc_2720_, 3, v_tailOff_2702_);
lean_ctor_set_usize(v_reuseFailAlloc_2720_, 4, v_shift_2701_);
v___x_2716_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2718_; 
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2716_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
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
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_tailOff_2702_);
lean_dec(v_size_2700_);
v_a_2722_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2710_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2710_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_del_object(v___x_2704_);
lean_dec(v_tailOff_2702_);
lean_dec(v_size_2700_);
lean_dec_ref(v_tail_2699_);
lean_dec_ref(v_ctx_x3f_2689_);
v_a_2730_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2706_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2706_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22___boxed(lean_object* v___x_2739_, lean_object* v_ctx_x3f_2740_, lean_object* v_t_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v___x_2739_, v_ctx_x3f_2740_, v_t_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___x_2739_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(lean_object* v___y_2750_, lean_object* v_ctx_x3f_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v_a_2757_, lean_object* v_a_x3f_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v_infoState_2761_; lean_object* v_trees_2762_; lean_object* v___x_2763_; 
v___x_2760_ = lean_st_ref_get(v___y_2750_);
v_infoState_2761_ = lean_ctor_get(v___x_2760_, 7);
lean_inc_ref(v_infoState_2761_);
lean_dec(v___x_2760_);
v_trees_2762_ = lean_ctor_get(v_infoState_2761_, 2);
lean_inc_ref(v_trees_2762_);
v___x_2763_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__22(v_infoState_2761_, v_ctx_x3f_2751_, v_trees_2762_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2750_);
lean_dec_ref(v_infoState_2761_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2802_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2802_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2802_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v_infoState_2769_; lean_object* v_env_2770_; lean_object* v_nextMacroScope_2771_; lean_object* v_ngen_2772_; lean_object* v_auxDeclNGen_2773_; lean_object* v_traceState_2774_; lean_object* v_cache_2775_; lean_object* v_messages_2776_; lean_object* v_snapshotTasks_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2801_; 
v___x_2768_ = lean_st_ref_take(v___y_2750_);
v_infoState_2769_ = lean_ctor_get(v___x_2768_, 7);
v_env_2770_ = lean_ctor_get(v___x_2768_, 0);
v_nextMacroScope_2771_ = lean_ctor_get(v___x_2768_, 1);
v_ngen_2772_ = lean_ctor_get(v___x_2768_, 2);
v_auxDeclNGen_2773_ = lean_ctor_get(v___x_2768_, 3);
v_traceState_2774_ = lean_ctor_get(v___x_2768_, 4);
v_cache_2775_ = lean_ctor_get(v___x_2768_, 5);
v_messages_2776_ = lean_ctor_get(v___x_2768_, 6);
v_snapshotTasks_2777_ = lean_ctor_get(v___x_2768_, 8);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2779_ = v___x_2768_;
v_isShared_2780_ = v_isSharedCheck_2801_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_snapshotTasks_2777_);
lean_inc(v_infoState_2769_);
lean_inc(v_messages_2776_);
lean_inc(v_cache_2775_);
lean_inc(v_traceState_2774_);
lean_inc(v_auxDeclNGen_2773_);
lean_inc(v_ngen_2772_);
lean_inc(v_nextMacroScope_2771_);
lean_inc(v_env_2770_);
lean_dec(v___x_2768_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2801_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
uint8_t v_enabled_2781_; lean_object* v_assignment_2782_; lean_object* v_lazyAssignment_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2799_; 
v_enabled_2781_ = lean_ctor_get_uint8(v_infoState_2769_, sizeof(void*)*3);
v_assignment_2782_ = lean_ctor_get(v_infoState_2769_, 0);
v_lazyAssignment_2783_ = lean_ctor_get(v_infoState_2769_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_infoState_2769_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v_infoState_2769_, 2);
lean_dec(v_unused_2800_);
v___x_2785_ = v_infoState_2769_;
v_isShared_2786_ = v_isSharedCheck_2799_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_lazyAssignment_2783_);
lean_inc(v_assignment_2782_);
lean_dec(v_infoState_2769_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2799_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = l_Lean_PersistentArray_append___redArg(v_a_2757_, v_a_2764_);
lean_dec(v_a_2764_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 2, v___x_2787_);
v___x_2789_ = v___x_2785_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_assignment_2782_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_lazyAssignment_2783_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v___x_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2798_, sizeof(void*)*3, v_enabled_2781_);
v___x_2789_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 7, v___x_2789_);
v___x_2791_ = v___x_2779_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_env_2770_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_nextMacroScope_2771_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_ngen_2772_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_auxDeclNGen_2773_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v_traceState_2774_);
lean_ctor_set(v_reuseFailAlloc_2797_, 5, v_cache_2775_);
lean_ctor_set(v_reuseFailAlloc_2797_, 6, v_messages_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 7, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2797_, 8, v_snapshotTasks_2777_);
v___x_2791_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2792_ = lean_st_ref_put(v___y_2750_, v___x_2791_);
v___x_2793_ = lean_box(0);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2793_);
v___x_2795_ = v___x_2766_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
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
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref(v_a_2757_);
v_a_2803_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2763_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2763_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v___y_2811_, lean_object* v_ctx_x3f_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v_a_2818_, lean_object* v_a_x3f_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2811_, v_ctx_x3f_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v_a_2818_, v_a_x3f_2819_);
lean_dec(v_a_x3f_2819_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2811_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v_infoState_2825_; lean_object* v_trees_2826_; lean_object* v___x_2827_; lean_object* v_infoState_2828_; lean_object* v_env_2829_; lean_object* v_nextMacroScope_2830_; lean_object* v_ngen_2831_; lean_object* v_auxDeclNGen_2832_; lean_object* v_traceState_2833_; lean_object* v_cache_2834_; lean_object* v_messages_2835_; lean_object* v_snapshotTasks_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2859_; 
v___x_2824_ = lean_st_ref_get(v___y_2822_);
v_infoState_2825_ = lean_ctor_get(v___x_2824_, 7);
lean_inc_ref(v_infoState_2825_);
lean_dec(v___x_2824_);
v_trees_2826_ = lean_ctor_get(v_infoState_2825_, 2);
lean_inc_ref(v_trees_2826_);
lean_dec_ref(v_infoState_2825_);
v___x_2827_ = lean_st_ref_take(v___y_2822_);
v_infoState_2828_ = lean_ctor_get(v___x_2827_, 7);
v_env_2829_ = lean_ctor_get(v___x_2827_, 0);
v_nextMacroScope_2830_ = lean_ctor_get(v___x_2827_, 1);
v_ngen_2831_ = lean_ctor_get(v___x_2827_, 2);
v_auxDeclNGen_2832_ = lean_ctor_get(v___x_2827_, 3);
v_traceState_2833_ = lean_ctor_get(v___x_2827_, 4);
v_cache_2834_ = lean_ctor_get(v___x_2827_, 5);
v_messages_2835_ = lean_ctor_get(v___x_2827_, 6);
v_snapshotTasks_2836_ = lean_ctor_get(v___x_2827_, 8);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2838_ = v___x_2827_;
v_isShared_2839_ = v_isSharedCheck_2859_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_snapshotTasks_2836_);
lean_inc(v_infoState_2828_);
lean_inc(v_messages_2835_);
lean_inc(v_cache_2834_);
lean_inc(v_traceState_2833_);
lean_inc(v_auxDeclNGen_2832_);
lean_inc(v_ngen_2831_);
lean_inc(v_nextMacroScope_2830_);
lean_inc(v_env_2829_);
lean_dec(v___x_2827_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2859_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v_enabled_2840_; lean_object* v_assignment_2841_; lean_object* v_lazyAssignment_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2857_; 
v_enabled_2840_ = lean_ctor_get_uint8(v_infoState_2828_, sizeof(void*)*3);
v_assignment_2841_ = lean_ctor_get(v_infoState_2828_, 0);
v_lazyAssignment_2842_ = lean_ctor_get(v_infoState_2828_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_infoState_2828_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v_infoState_2828_, 2);
lean_dec(v_unused_2858_);
v___x_2844_ = v_infoState_2828_;
v_isShared_2845_ = v_isSharedCheck_2857_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_lazyAssignment_2842_);
lean_inc(v_assignment_2841_);
lean_dec(v_infoState_2828_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2857_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2846_ = lean_unsigned_to_nat(32u);
v___x_2847_ = lean_mk_empty_array_with_capacity(v___x_2846_);
lean_dec_ref(v___x_2847_);
v___x_2848_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3___closed__1);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 2, v___x_2848_);
v___x_2850_ = v___x_2844_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_assignment_2841_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_lazyAssignment_2842_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v___x_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2856_, sizeof(void*)*3, v_enabled_2840_);
v___x_2850_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2852_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 7, v___x_2850_);
v___x_2852_ = v___x_2838_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_env_2829_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_nextMacroScope_2830_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_ngen_2831_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_auxDeclNGen_2832_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_traceState_2833_);
lean_ctor_set(v_reuseFailAlloc_2855_, 5, v_cache_2834_);
lean_ctor_set(v_reuseFailAlloc_2855_, 6, v_messages_2835_);
lean_ctor_set(v_reuseFailAlloc_2855_, 7, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2855_, 8, v_snapshotTasks_2836_);
v___x_2852_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_st_ref_put(v___y_2822_, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_trees_2826_);
return v___x_2854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg___boxed(lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2860_);
lean_dec(v___y_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(lean_object* v_x_2863_, lean_object* v_ctx_x3f_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; lean_object* v_infoState_2873_; uint8_t v_enabled_2874_; 
v___x_2872_ = lean_st_ref_get(v___y_2870_);
v_infoState_2873_ = lean_ctor_get(v___x_2872_, 7);
lean_inc_ref(v_infoState_2873_);
lean_dec(v___x_2872_);
v_enabled_2874_ = lean_ctor_get_uint8(v_infoState_2873_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2873_);
if (v_enabled_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_dec_ref(v_ctx_x3f_2864_);
lean_inc(v___y_2870_);
lean_inc_ref(v___y_2869_);
lean_inc(v___y_2868_);
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
v___x_2875_ = lean_apply_7(v_x_2863_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, lean_box(0));
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v_r_2878_; 
v___x_2876_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_2870_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
lean_inc(v___y_2870_);
lean_inc_ref(v___y_2869_);
lean_inc(v___y_2868_);
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
v_r_2878_ = lean_apply_7(v_x_2863_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, lean_box(0));
if (lean_obj_tag(v_r_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2903_; 
v_a_2879_ = lean_ctor_get(v_r_2878_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_r_2878_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2881_ = v_r_2878_;
v_isShared_2882_ = v_isSharedCheck_2903_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v_r_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2903_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
lean_inc(v_a_2879_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 1);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2870_, v_ctx_x3f_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v_a_2877_, v___x_2884_);
lean_dec_ref(v___x_2884_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2893_);
v___x_2887_ = v___x_2885_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v___x_2885_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_a_2879_);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2879_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_a_2879_);
v_a_2894_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2885_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2885_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2904_ = lean_ctor_get(v_r_2878_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v_r_2878_, 1);
v___x_2905_ = lean_box(0);
v___x_2906_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___lam__0(v___y_2870_, v_ctx_x3f_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v_a_2877_, v___x_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v___x_2906_, 0);
lean_dec(v_unused_2914_);
v___x_2908_ = v___x_2906_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v___x_2906_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 1);
lean_ctor_set(v___x_2908_, 0, v_a_2904_);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2904_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2904_);
v_a_2915_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2906_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2906_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg___boxed(lean_object* v_x_2923_, lean_object* v_ctx_x3f_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2923_, v_ctx_x3f_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(lean_object* v_x_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___f_2942_; lean_object* v___x_2943_; 
v___f_2942_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___closed__0));
v___x_2943_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_2934_, v___f_2942_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg___boxed(lean_object* v_x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(lean_object* v_00_u03b1_2953_, lean_object* v_x_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___redArg(v_x_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed(lean_object* v_00_u03b1_2963_, lean_object* v_x_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6(v_00_u03b1_2963_, v_x_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
return v_res_2972_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__1(void){
_start:
{
lean_object* v_fields_2975_; lean_object* v_seenFields_2976_; lean_object* v___x_2977_; 
v_fields_2975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__0));
v_seenFields_2976_ = l_Lean_NameSet_empty;
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_seenFields_2976_);
lean_ctor_set(v___x_2977_, 1, v_fields_2975_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConfig___closed__2(void){
_start:
{
lean_object* v___x_2978_; lean_object* v_source_x3f_2979_; lean_object* v___x_2980_; 
v___x_2978_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__1, &l_Lean_Elab_Tactic_elabConfig___closed__1_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__1);
v_source_x3f_2979_ = lean_box(0);
v___x_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_source_x3f_2979_);
lean_ctor_set(v___x_2980_, 1, v___x_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t v_recover_2983_, lean_object* v_structName_2984_, lean_object* v_items_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; size_t v_sz_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___f_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_2993_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___closed__3);
v___x_2994_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___closed__0));
v___x_2995_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConfig___closed__2, &l_Lean_Elab_Tactic_elabConfig___closed__2_once, _init_l_Lean_Elab_Tactic_elabConfig___closed__2);
v_sz_2996_ = lean_array_size(v_items_2985_);
v___x_2997_ = lean_box(v_recover_2983_);
v___x_2998_ = lean_box_usize(v_sz_2996_);
v___x_2999_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConfig___boxed__const__1));
v___f_3000_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabConfig___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3000_, 0, v_structName_2984_);
lean_closure_set(v___f_3000_, 1, v___x_2997_);
lean_closure_set(v___f_3000_, 2, v_items_2985_);
lean_closure_set(v___f_3000_, 3, v___x_2998_);
lean_closure_set(v___f_3000_, 4, v___x_2999_);
lean_closure_set(v___f_3000_, 5, v___x_2995_);
v___x_3001_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6___boxed), 9, 2);
lean_closure_set(v___x_3001_, 0, lean_box(0));
lean_closure_set(v___x_3001_, 1, v___f_3000_);
v___x_3002_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Elab_Tactic_elabConfig_spec__7___boxed), 11, 4);
lean_closure_set(v___x_3002_, 0, lean_box(0));
lean_closure_set(v___x_3002_, 1, v___x_2993_);
lean_closure_set(v___x_3002_, 2, v___x_2994_);
lean_closure_set(v___x_3002_, 3, v___x_3001_);
v___x_3003_ = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at___00Lean_Elab_Tactic_elabConfig_spec__8___redArg(v___x_3002_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConfig___boxed(lean_object* v_recover_3004_, lean_object* v_structName_3005_, lean_object* v_items_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
uint8_t v_recover_boxed_3014_; lean_object* v_res_3015_; 
v_recover_boxed_3014_ = lean_unbox(v_recover_3004_);
v_res_3015_ = l_Lean_Elab_Tactic_elabConfig(v_recover_boxed_3014_, v_structName_3005_, v_items_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(lean_object* v_00_u03b1_3016_, lean_object* v_ref_3017_, lean_object* v_msg_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___redArg(v_ref_3017_, v_msg_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3___boxed(lean_object* v_00_u03b1_3027_, lean_object* v_ref_3028_, lean_object* v_msg_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3(v_00_u03b1_3027_, v_ref_3028_, v_msg_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v_ref_3028_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(lean_object* v_t_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___redArg(v_t_3038_, v___y_3044_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9___boxed(lean_object* v_t_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00Lean_Elab_Tactic_elabConfig_spec__1_spec__3_spec__9(v_t_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(lean_object* v_00_u03b1_3056_, lean_object* v_constName_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___redArg(v_constName_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3066_, lean_object* v_constName_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5(v_00_u03b1_3066_, v_constName_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(lean_object* v_00_u03b1_3076_, lean_object* v_msg_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___redArg(v_msg_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3086_, lean_object* v_msg_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7(v_00_u03b1_3086_, v_msg_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___redArg(v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19___boxed(lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__11_spec__19(v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___redArg(v___y_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21___boxed(lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12_spec__21(v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(lean_object* v_00_u03b1_3128_, lean_object* v_x_3129_, lean_object* v_ctx_x3f_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___redArg(v_x_3129_, v_ctx_x3f_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3139_, lean_object* v_x_3140_, lean_object* v_ctx_x3f_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_elabConfig_spec__6_spec__12(v_00_u03b1_3139_, v_x_3140_, v_ctx_x3f_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(lean_object* v_ref_3150_, lean_object* v_msgData_3151_, uint8_t v_severity_3152_, uint8_t v_isSilent_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___redArg(v_ref_3150_, v_msgData_3151_, v_severity_3152_, v_isSilent_3153_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4___boxed(lean_object* v_ref_3162_, lean_object* v_msgData_3163_, lean_object* v_severity_3164_, lean_object* v_isSilent_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
uint8_t v_severity_boxed_3173_; uint8_t v_isSilent_boxed_3174_; lean_object* v_res_3175_; 
v_severity_boxed_3173_ = lean_unbox(v_severity_3164_);
v_isSilent_boxed_3174_ = lean_unbox(v_isSilent_3165_);
v_res_3175_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_elabConfig_spec__0_spec__0_spec__4(v_ref_3162_, v_msgData_3163_, v_severity_boxed_3173_, v_isSilent_boxed_3174_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v_ref_3162_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(lean_object* v_00_u03b1_3176_, lean_object* v_ref_3177_, lean_object* v_constName_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___redArg(v_ref_3177_, v_constName_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b1_3187_, lean_object* v_ref_3188_, lean_object* v_constName_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12(v_00_u03b1_3187_, v_ref_3188_, v_constName_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(lean_object* v_msgData_3198_, lean_object* v_macroStack_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___redArg(v_msgData_3198_, v_macroStack_3199_, v___y_3204_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15___boxed(lean_object* v_msgData_3208_, lean_object* v_macroStack_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabConfig_spec__3_spec__7_spec__15(v_msgData_3208_, v_macroStack_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(lean_object* v_00_u03b1_3218_, lean_object* v_ref_3219_, lean_object* v_msg_3220_, lean_object* v_declHint_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___redArg(v_ref_3219_, v_msg_3220_, v_declHint_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17___boxed(lean_object* v_00_u03b1_3230_, lean_object* v_ref_3231_, lean_object* v_msg_3232_, lean_object* v_declHint_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17(v_00_u03b1_3230_, v_ref_3231_, v_msg_3232_, v_declHint_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v_ref_3231_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(lean_object* v_msg_3242_, lean_object* v_declHint_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___redArg(v_msg_3242_, v_declHint_3243_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26___boxed(lean_object* v_msg_3252_, lean_object* v_declHint_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_elabConfig_spec__2_spec__5_spec__12_spec__17_spec__23_spec__26(v_msg_3252_, v_declHint_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3261_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__11));
v___x_3295_ = l_String_toRawSubstring_x27(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__18));
v___x_3312_ = l_String_toRawSubstring_x27(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__21));
v___x_3317_ = l_String_toRawSubstring_x27(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__31));
v___x_3342_ = l_String_toRawSubstring_x27(v___x_3341_);
return v___x_3342_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__39));
v___x_3364_ = l_String_toRawSubstring_x27(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__48));
v___x_3387_ = l_String_toRawSubstring_x27(v___x_3386_);
return v___x_3387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3398_ = l_String_toRawSubstring_x27(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__71));
v___x_3442_ = l_String_toRawSubstring_x27(v___x_3441_);
return v___x_3442_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__77));
v___x_3454_ = l_String_toRawSubstring_x27(v___x_3453_);
return v___x_3454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__83));
v___x_3469_ = l_String_toRawSubstring_x27(v___x_3468_);
return v___x_3469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__89));
v___x_3485_ = l_String_toRawSubstring_x27(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__114));
v___x_3553_ = l_String_toRawSubstring_x27(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__117));
v___x_3558_ = l_String_toRawSubstring_x27(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__122));
v___x_3568_ = l_String_toRawSubstring_x27(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__128));
v___x_3582_ = l_String_toRawSubstring_x27(v___x_3581_);
return v___x_3582_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__131));
v___x_3587_ = l_String_toRawSubstring_x27(v___x_3586_);
return v___x_3587_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__139));
v___x_3609_ = l_String_toRawSubstring_x27(v___x_3608_);
return v___x_3609_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__150));
v___x_3638_ = l_String_toRawSubstring_x27(v___x_3637_);
return v___x_3638_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__168));
v___x_3679_ = l_String_toRawSubstring_x27(v___x_3678_);
return v___x_3679_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__175));
v___x_3695_ = l_String_toRawSubstring_x27(v___x_3694_);
return v___x_3695_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__190));
v___x_3718_ = l_String_toRawSubstring_x27(v___x_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__198));
v___x_3737_ = l_String_toRawSubstring_x27(v___x_3736_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201(void){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__17));
v___x_3741_ = l_String_toRawSubstring_x27(v___x_3740_);
return v___x_3741_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__209));
v___x_3764_ = l_String_toRawSubstring_x27(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__212));
v___x_3769_ = l_String_toRawSubstring_x27(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__220));
v___x_3790_ = l_String_toRawSubstring_x27(v___x_3789_);
return v___x_3790_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__224));
v___x_3797_ = l_String_toRawSubstring_x27(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__232));
v___x_3812_ = l_String_toRawSubstring_x27(v___x_3811_);
return v___x_3812_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__238));
v___x_3824_ = l_String_toRawSubstring_x27(v___x_3823_);
return v___x_3824_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243(void){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__242));
v___x_3830_ = l_String_toRawSubstring_x27(v___x_3829_);
return v___x_3830_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__246));
v___x_3836_ = l_String_toRawSubstring_x27(v___x_3835_);
return v___x_3836_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254(void){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__253));
v___x_3851_ = l_String_toRawSubstring_x27(v___x_3850_);
return v___x_3851_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__15));
v___x_3857_ = l_String_toRawSubstring_x27(v___x_3856_);
return v___x_3857_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__261));
v___x_3868_ = l_String_toRawSubstring_x27(v___x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(lean_object* v_doc_x3f_3883_, lean_object* v_elabName_3884_, lean_object* v_type_3885_, lean_object* v_monadName_3886_, lean_object* v_adapt_3887_, lean_object* v_recover_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v_quotContext_3891_; lean_object* v_currMacroScope_3892_; lean_object* v_ref_3893_; lean_object* v_ref_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___y_4031_; 
v_quotContext_3891_ = lean_ctor_get(v_a_3889_, 1);
v_currMacroScope_3892_ = lean_ctor_get(v_a_3889_, 2);
v_ref_3893_ = lean_ctor_get(v_a_3889_, 5);
v_ref_3894_ = l_Lean_replaceRef(v_type_3885_, v_ref_3893_);
v___x_3895_ = 0;
v___x_3896_ = l_Lean_SourceInfo_fromRef(v_ref_3894_, v___x_3895_);
lean_dec(v_ref_3894_);
v___x_3897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__2));
v___x_3898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__3));
lean_inc_n(v___x_3896_, 7);
v___x_3899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3896_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__5));
v___x_3901_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__6);
v___x_3902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3896_);
lean_ctor_set(v___x_3902_, 1, v___x_3900_);
lean_ctor_set(v___x_3902_, 2, v___x_3901_);
v___x_3903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__8));
lean_inc_ref_n(v___x_3902_, 2);
v___x_3904_ = l_Lean_Syntax_node1(v___x_3896_, v___x_3903_, v___x_3902_);
v___x_3905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__11));
v___x_3906_ = l_Lean_Syntax_node1(v___x_3896_, v___x_3905_, v___x_3902_);
v___x_3907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__12));
v___x_3908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3896_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
lean_inc_n(v_type_3885_, 3);
v___x_3909_ = l_Lean_Syntax_node2(v___x_3896_, v___x_3900_, v___x_3908_, v_type_3885_);
v___x_3910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__0___closed__13));
v___x_3911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3896_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = l_Lean_Syntax_node6(v___x_3896_, v___x_3897_, v___x_3899_, v___x_3902_, v___x_3904_, v___x_3906_, v___x_3909_, v___x_3911_);
v___x_3913_ = l_Lean_SourceInfo_fromRef(v_ref_3893_, v___x_3895_);
v___x_3914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__1));
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__3));
lean_inc_n(v___x_3913_, 55);
v___x_3916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3913_);
lean_ctor_set(v___x_3916_, 1, v___x_3900_);
lean_ctor_set(v___x_3916_, 2, v___x_3901_);
v___x_3917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__4));
v___x_3918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__5));
v___x_3919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3913_);
lean_ctor_set(v___x_3919_, 1, v___x_3917_);
v___x_3920_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3918_, v___x_3919_);
v___x_3921_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3920_);
lean_inc_ref_n(v___x_3916_, 21);
v___x_3922_ = l_Lean_Syntax_node7(v___x_3913_, v___x_3915_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3921_, v___x_3916_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__7));
v___x_3924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__8));
v___x_3925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3913_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__10));
v___x_3927_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__12);
v___x_3928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__13));
lean_inc_n(v_currMacroScope_3892_, 9);
lean_inc_n(v_quotContext_3891_, 9);
v___x_3929_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3928_, v_currMacroScope_3892_);
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3913_);
lean_ctor_set(v___x_3931_, 1, v___x_3927_);
lean_ctor_set(v___x_3931_, 2, v___x_3929_);
lean_ctor_set(v___x_3931_, 3, v___x_3930_);
lean_inc_ref(v___x_3931_);
v___x_3932_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3926_, v___x_3931_, v___x_3916_);
v___x_3933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__15));
v___x_3934_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__17));
v___x_3935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
v___x_3936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3913_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__19);
v___x_3938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__20));
v___x_3939_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3938_, v_currMacroScope_3892_);
v___x_3940_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3913_);
lean_ctor_set(v___x_3940_, 1, v___x_3937_);
lean_ctor_set(v___x_3940_, 2, v___x_3939_);
lean_ctor_set(v___x_3940_, 3, v___x_3930_);
lean_inc_ref(v___x_3940_);
v___x_3941_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3940_);
v___x_3942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3913_);
lean_ctor_set(v___x_3942_, 1, v___x_3907_);
v___x_3943_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__22);
v___x_3944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__23));
v___x_3945_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3944_, v_currMacroScope_3892_);
v___x_3946_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__28));
v___x_3947_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3913_);
lean_ctor_set(v___x_3947_, 1, v___x_3943_);
lean_ctor_set(v___x_3947_, 2, v___x_3945_);
lean_ctor_set(v___x_3947_, 3, v___x_3946_);
lean_inc_ref_n(v___x_3942_, 2);
v___x_3948_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_3942_, v___x_3947_);
v___x_3949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_3950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3913_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
lean_inc_ref_n(v___x_3950_, 2);
lean_inc_ref_n(v___x_3936_, 2);
v___x_3951_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3934_, v___x_3936_, v___x_3941_, v___x_3948_, v___x_3916_, v___x_3950_);
v___x_3952_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3951_);
v___x_3953_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__30));
v___x_3954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__12));
v___x_3955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__32);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__33));
v___x_3957_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3956_, v_currMacroScope_3892_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__36));
v___x_3959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3913_);
lean_ctor_set(v___x_3959_, 1, v___x_3955_);
lean_ctor_set(v___x_3959_, 2, v___x_3957_);
lean_ctor_set(v___x_3959_, 3, v___x_3958_);
v___x_3960_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v_type_3885_);
lean_inc(v___x_3960_);
v___x_3961_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_3959_, v___x_3960_);
v___x_3962_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3953_, v___x_3942_, v___x_3961_);
lean_inc(v___x_3962_);
v___x_3963_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3962_);
lean_inc(v___x_3963_);
lean_inc(v___x_3952_);
v___x_3964_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3933_, v___x_3952_, v___x_3963_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__38));
v___x_3966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__1___closed__6));
v___x_3967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3913_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__40);
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__42));
v___x_3970_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3969_, v_currMacroScope_3892_);
v___x_3971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__45));
v___x_3972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3913_);
lean_ctor_set(v___x_3972_, 1, v___x_3968_);
lean_ctor_set(v___x_3972_, 2, v___x_3970_);
lean_ctor_set(v___x_3972_, 3, v___x_3971_);
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__47));
v___x_3974_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__49);
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__50));
v___x_3976_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3975_, v_currMacroScope_3892_);
v___x_3977_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3913_);
lean_ctor_set(v___x_3977_, 1, v___x_3974_);
lean_ctor_set(v___x_3977_, 2, v___x_3976_);
lean_ctor_set(v___x_3977_, 3, v___x_3930_);
v___x_3978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__52));
v___x_3979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_3980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3913_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__54);
v___x_3982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__55));
v___x_3983_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3982_, v_currMacroScope_3892_);
v___x_3984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3913_);
lean_ctor_set(v___x_3984_, 1, v___x_3981_);
lean_ctor_set(v___x_3984_, 2, v___x_3983_);
lean_ctor_set(v___x_3984_, 3, v___x_3930_);
lean_inc_ref(v___x_3980_);
v___x_3985_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3978_, v___x_3980_, v___x_3984_);
lean_inc_ref_n(v___x_3967_, 2);
v___x_3986_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3973_, v___x_3936_, v___x_3977_, v___x_3967_, v___x_3985_, v___x_3950_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__57));
v___x_3988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_expandFieldName___closed__12));
v___x_3989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3913_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
lean_inc_ref(v___x_3989_);
v___x_3990_ = l_Lean_Syntax_node3(v___x_3913_, v___x_3987_, v___x_3989_, v___x_3989_, v_type_3885_);
lean_inc(v___x_3990_);
v___x_3991_ = l_Lean_Syntax_node4(v___x_3913_, v___x_3900_, v___x_3986_, v_type_3885_, v___x_3990_, v___x_3940_);
v___x_3992_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_3972_, v___x_3991_);
v___x_3993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__60));
v___x_3994_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3993_, v___x_3916_, v___x_3916_);
lean_inc(v___x_3994_);
v___x_3995_ = l_Lean_Syntax_node4(v___x_3913_, v___x_3965_, v___x_3967_, v___x_3992_, v___x_3994_, v___x_3916_);
lean_inc_ref(v___x_3925_);
v___x_3996_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3923_, v___x_3925_, v___x_3932_, v___x_3964_, v___x_3995_, v___x_3916_);
v___x_3997_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3914_, v___x_3922_, v___x_3996_);
v___x_3998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__62));
v___x_3999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__63));
v___x_4000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3913_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__65));
v___x_4002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__67));
v___x_4003_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4002_, v___x_3916_);
v___x_4004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__70));
v___x_4005_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__72);
v___x_4006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__73));
v___x_4007_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4006_, v_currMacroScope_3892_);
v___x_4008_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4008_, 0, v___x_3913_);
lean_ctor_set(v___x_4008_, 1, v___x_4005_);
lean_ctor_set(v___x_4008_, 2, v___x_4007_);
lean_ctor_set(v___x_4008_, 3, v___x_3930_);
v___x_4009_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3931_);
v___x_4010_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4004_, v___x_4008_, v___x_4009_);
v___x_4011_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4001_, v___x_4003_, v___x_4010_);
v___x_4012_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4011_);
v___x_4013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__74));
v___x_4014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_3913_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = l_Lean_Syntax_node3(v___x_3913_, v___x_3998_, v___x_4000_, v___x_4012_, v___x_4014_);
v___x_4016_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4015_);
v___x_4017_ = l_Lean_Syntax_node7(v___x_3913_, v___x_3915_, v___x_3916_, v___x_4016_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_);
v___x_4018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__75));
v___x_4019_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__76));
v___x_4020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_3913_);
lean_ctor_set(v___x_4020_, 1, v___x_4018_);
v___x_4021_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__78);
v___x_4022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__79));
v___x_4023_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4022_, v_currMacroScope_3892_);
v___x_4024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4024_, 0, v___x_3913_);
lean_ctor_set(v___x_4024_, 1, v___x_4021_);
lean_ctor_set(v___x_4024_, 2, v___x_4023_);
lean_ctor_set(v___x_4024_, 3, v___x_3930_);
lean_inc_ref(v___x_4024_);
v___x_4025_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3926_, v___x_4024_, v___x_3916_);
v___x_4026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__81));
v___x_4027_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4026_, v___x_3952_, v___x_3962_);
v___x_4028_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4019_, v___x_4020_, v___x_4025_, v___x_4027_, v___x_3916_);
v___x_4029_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3914_, v___x_4017_, v___x_4028_);
if (lean_obj_tag(v_doc_x3f_3883_) == 1)
{
lean_object* v_val_4361_; lean_object* v___x_4362_; 
v_val_4361_ = lean_ctor_get(v_doc_x3f_3883_, 0);
lean_inc(v_val_4361_);
lean_dec_ref_known(v_doc_x3f_3883_, 1);
v___x_4362_ = l_Array_mkArray1___redArg(v_val_4361_);
v___y_4031_ = v___x_4362_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4363_; 
lean_dec(v_doc_x3f_3883_);
v___x_4363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__268));
v___y_4031_ = v___x_4363_;
goto v___jp_4030_;
}
v___jp_4030_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4032_ = l_Array_append___redArg(v___x_3901_, v___y_4031_);
lean_dec_ref(v___y_4031_);
lean_inc_n(v___x_3913_, 183);
v___x_4033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4033_, 0, v___x_3913_);
lean_ctor_set(v___x_4033_, 1, v___x_3900_);
lean_ctor_set(v___x_4033_, 2, v___x_4032_);
lean_inc_ref_n(v___x_3916_, 57);
v___x_4034_ = l_Lean_Syntax_node7(v___x_3913_, v___x_3915_, v___x_4033_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_, v___x_3916_);
v___x_4035_ = lean_box(2);
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__82));
v___x_4037_ = lean_unsigned_to_nat(2u);
v___x_4038_ = lean_mk_empty_array_with_capacity(v___x_4037_);
v___x_4039_ = lean_array_push(v___x_4038_, v_elabName_3884_);
v___x_4040_ = lean_array_push(v___x_4039_, v___x_4036_);
v___x_4041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4035_);
lean_ctor_set(v___x_4041_, 1, v___x_3926_);
lean_ctor_set(v___x_4041_, 2, v___x_4040_);
v___x_4042_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__84);
v___x_4043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__85));
lean_inc_n(v_currMacroScope_3892_, 26);
lean_inc_n(v_quotContext_3891_, 26);
v___x_4044_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4043_, v_currMacroScope_3892_);
v___x_4045_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__88));
v___x_4046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4046_, 0, v___x_3913_);
lean_ctor_set(v___x_4046_, 1, v___x_4042_);
lean_ctor_set(v___x_4046_, 2, v___x_4044_);
lean_ctor_set(v___x_4046_, 3, v___x_4045_);
lean_inc_ref(v___x_4046_);
v___x_4047_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4046_);
v___x_4048_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__90);
v___x_4049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__91));
v___x_4050_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4049_, v_currMacroScope_3892_);
v___x_4051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__96));
v___x_4052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4052_, 0, v___x_3913_);
lean_ctor_set(v___x_4052_, 1, v___x_4048_);
lean_ctor_set(v___x_4052_, 2, v___x_4050_);
lean_ctor_set(v___x_4052_, 3, v___x_4051_);
lean_inc_ref(v___x_3942_);
v___x_4053_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_3942_, v___x_4052_);
lean_inc_ref_n(v___x_3950_, 3);
lean_inc(v___x_4047_);
lean_inc_ref_n(v___x_3936_, 2);
v___x_4054_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3934_, v___x_3936_, v___x_4047_, v___x_4053_, v___x_3916_, v___x_3950_);
v___x_4055_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4054_);
v___x_4056_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v_monadName_3886_, v___x_3960_);
v___x_4057_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3953_, v___x_3942_, v___x_4056_);
v___x_4058_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4057_);
v___x_4059_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3933_, v___x_4055_, v___x_4058_);
v___x_4060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__97));
v___x_4061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__98));
v___x_4062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_3913_);
lean_ctor_set(v___x_4062_, 1, v___x_4060_);
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__100));
v___x_4064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__102));
v___x_4065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__104));
v___x_4066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__105));
v___x_4067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_3913_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__107));
v___x_4069_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4068_, v___x_3916_);
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__109));
v___x_4071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__111));
v___x_4072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__113));
v___x_4073_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4075_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4074_, v_currMacroScope_3892_);
v___x_4076_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4076_, 0, v___x_3913_);
lean_ctor_set(v___x_4076_, 1, v___x_4073_);
lean_ctor_set(v___x_4076_, 2, v___x_4075_);
lean_ctor_set(v___x_4076_, 3, v___x_3930_);
lean_inc_ref(v___x_4076_);
v___x_4077_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4072_, v___x_4076_);
lean_inc_ref_n(v___x_3967_, 5);
v___x_4078_ = l_Lean_Syntax_node5(v___x_3913_, v___x_4071_, v___x_4077_, v___x_3916_, v___x_3916_, v___x_3967_, v_recover_3888_);
v___x_4079_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4070_, v___x_4078_);
lean_inc_n(v___x_4069_, 5);
lean_inc_ref_n(v___x_4067_, 5);
v___x_4080_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4065_, v___x_4067_, v___x_3916_, v___x_4069_, v___x_4079_);
v___x_4081_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4080_, v___x_3916_);
v___x_4082_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__118);
v___x_4083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__119));
v___x_4084_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4083_, v_currMacroScope_3892_);
v___x_4085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__121));
v___x_4086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4086_, 0, v___x_3913_);
lean_ctor_set(v___x_4086_, 1, v___x_4082_);
lean_ctor_set(v___x_4086_, 2, v___x_4084_);
lean_ctor_set(v___x_4086_, 3, v___x_4085_);
lean_inc_ref(v___x_4086_);
v___x_4087_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4072_, v___x_4086_);
v___x_4088_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__123);
v___x_4089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__124));
v___x_4090_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4089_, v_currMacroScope_3892_);
v___x_4091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__127));
v___x_4092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4092_, 0, v___x_3913_);
lean_ctor_set(v___x_4092_, 1, v___x_4088_);
lean_ctor_set(v___x_4092_, 2, v___x_4090_);
lean_ctor_set(v___x_4092_, 3, v___x_4091_);
v___x_4093_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__129);
v___x_4094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__130));
v___x_4095_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4094_, v_currMacroScope_3892_);
v___x_4096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4096_, 0, v___x_3913_);
lean_ctor_set(v___x_4096_, 1, v___x_4093_);
lean_ctor_set(v___x_4096_, 2, v___x_4095_);
lean_ctor_set(v___x_4096_, 3, v___x_3930_);
lean_inc_ref(v___x_4096_);
v___x_4097_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4072_, v___x_4096_);
v___x_4098_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__132);
v___x_4099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__133));
v___x_4100_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4099_, v_currMacroScope_3892_);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__136));
v___x_4102_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4102_, 0, v___x_3913_);
lean_ctor_set(v___x_4102_, 1, v___x_4098_);
lean_ctor_set(v___x_4102_, 2, v___x_4100_);
lean_ctor_set(v___x_4102_, 3, v___x_4101_);
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4106_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4107_ = lean_box(0);
v___x_4108_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4107_, v_currMacroScope_3892_);
v___x_4109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4110_, 0, v___x_3913_);
lean_ctor_set(v___x_4110_, 1, v___x_4106_);
lean_ctor_set(v___x_4110_, 2, v___x_4108_);
lean_ctor_set(v___x_4110_, 3, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4105_, v___x_4110_);
v___x_4112_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4104_, v___x_3936_, v___x_4111_);
v___x_4113_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__140);
v___x_4114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__141));
v___x_4115_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4114_, v_currMacroScope_3892_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__144));
v___x_4117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4117_, 0, v___x_3913_);
lean_ctor_set(v___x_4117_, 1, v___x_4113_);
lean_ctor_set(v___x_4117_, 2, v___x_4115_);
lean_ctor_set(v___x_4117_, 3, v___x_4116_);
v___x_4118_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4117_, v___x_4047_);
lean_inc(v___x_4112_);
v___x_4119_ = l_Lean_Syntax_node3(v___x_3913_, v___x_4103_, v___x_4112_, v___x_4118_, v___x_3950_);
v___x_4120_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4119_);
v___x_4121_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4102_, v___x_4120_);
v___x_4122_ = l_Lean_Syntax_node5(v___x_3913_, v___x_4071_, v___x_4097_, v___x_3916_, v___x_3916_, v___x_3967_, v___x_4121_);
v___x_4123_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4070_, v___x_4122_);
v___x_4124_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4065_, v___x_4067_, v___x_3916_, v___x_4069_, v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4124_, v___x_3916_);
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__146));
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__147));
v___x_4128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_3913_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__149));
v___x_4130_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__151);
v___x_4131_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__153));
v___x_4132_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4131_, v_currMacroScope_3892_);
v___x_4133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4133_, 0, v___x_3913_);
lean_ctor_set(v___x_4133_, 1, v___x_4130_);
lean_ctor_set(v___x_4133_, 2, v___x_4132_);
lean_ctor_set(v___x_4133_, 3, v___x_3930_);
v___x_4134_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4129_, v___x_3916_, v___x_4133_);
v___x_4135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__154));
v___x_4136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_3913_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__156));
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__157));
v___x_4139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_3913_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3912_);
lean_inc_ref(v___x_4139_);
v___x_4141_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4137_, v___x_4139_, v___x_4140_);
v___x_4142_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4141_, v___x_3916_);
lean_inc(v___x_4142_);
v___x_4143_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4142_);
v___x_4144_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4143_);
lean_inc(v___x_4144_);
lean_inc_ref_n(v___x_4136_, 3);
lean_inc_ref_n(v___x_4128_, 3);
v___x_4145_ = l_Lean_Syntax_node6(v___x_3913_, v___x_4126_, v___x_4128_, v___x_4134_, v___x_4136_, v___x_4144_, v___x_3916_, v___x_3916_);
v___x_4146_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4145_, v___x_3916_);
v___x_4147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__159));
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__160));
v___x_4149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_3913_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
v___x_4150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_3913_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4155_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__169);
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__170));
v___x_4157_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4156_, v_currMacroScope_3892_);
v___x_4158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__174));
v___x_4159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4159_, 0, v___x_3913_);
lean_ctor_set(v___x_4159_, 1, v___x_4155_);
lean_ctor_set(v___x_4159_, 2, v___x_4157_);
lean_ctor_set(v___x_4159_, 3, v___x_4158_);
v___x_4160_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4159_);
lean_inc_ref_n(v___x_4153_, 2);
v___x_4161_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4151_, v___x_4153_, v___x_4160_);
v___x_4162_ = l_Lean_Syntax_node3(v___x_3913_, v___x_4103_, v___x_4112_, v___x_4161_, v___x_3950_);
v___x_4163_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__176);
v___x_4164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__177));
v___x_4165_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4164_, v_currMacroScope_3892_);
v___x_4166_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4166_, 0, v___x_3913_);
lean_ctor_set(v___x_4166_, 1, v___x_4163_);
lean_ctor_set(v___x_4166_, 2, v___x_4165_);
lean_ctor_set(v___x_4166_, 3, v___x_3930_);
v___x_4167_ = l_Lean_Syntax_node3(v___x_3913_, v___x_4150_, v___x_4162_, v___x_3980_, v___x_4166_);
lean_inc_n(v___x_3990_, 3);
v___x_4168_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_3990_);
v___x_4169_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4167_, v___x_4168_);
v___x_4170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__179));
v___x_4171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__180));
v___x_4172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_3913_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__182));
v___x_4174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__183));
v___x_4175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_3913_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__185));
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__187));
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__188));
v___x_4179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_3913_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4177_, v___x_4179_);
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__189));
v___x_4182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_3913_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4177_, v___x_4182_);
lean_inc(v___x_4183_);
v___x_4184_ = l_Lean_Syntax_node3(v___x_3913_, v___x_4176_, v___x_4180_, v___x_3990_, v___x_4183_);
lean_inc_ref_n(v___x_4175_, 2);
v___x_4185_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4173_, v___x_4175_, v___x_4184_);
lean_inc_ref_n(v___x_4172_, 2);
v___x_4186_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4170_, v___x_4172_, v___x_4185_);
v___x_4187_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4186_);
v___x_4188_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4187_, v___x_3916_);
v___x_4189_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4188_);
v___x_4190_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4189_);
lean_inc_ref_n(v___x_4062_, 2);
v___x_4191_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4147_, v___x_4149_, v___x_4169_, v___x_4062_, v___x_4190_);
v___x_4192_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4191_, v___x_3916_);
v___x_4193_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__191);
v___x_4194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__192));
v___x_4195_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4194_, v_currMacroScope_3892_);
v___x_4196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__197));
v___x_4197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4197_, 0, v___x_3913_);
lean_ctor_set(v___x_4197_, 1, v___x_4193_);
lean_ctor_set(v___x_4197_, 2, v___x_4195_);
lean_ctor_set(v___x_4197_, 3, v___x_4196_);
v___x_4198_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__199);
v___x_4199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__200));
v___x_4200_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4199_, v_currMacroScope_3892_);
v___x_4201_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4201_, 0, v___x_3913_);
lean_ctor_set(v___x_4201_, 1, v___x_4198_);
lean_ctor_set(v___x_4201_, 2, v___x_4200_);
lean_ctor_set(v___x_4201_, 3, v___x_3930_);
v___x_4202_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__201);
v___x_4203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__202));
v___x_4204_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4203_, v_currMacroScope_3892_);
v___x_4205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__204));
v___x_4206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4206_, 0, v___x_3913_);
lean_ctor_set(v___x_4206_, 1, v___x_4202_);
lean_ctor_set(v___x_4206_, 2, v___x_4204_);
lean_ctor_set(v___x_4206_, 3, v___x_4205_);
v___x_4207_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3973_, v___x_3936_, v___x_4201_, v___x_3967_, v___x_4206_, v___x_3950_);
v___x_4208_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_4207_, v___x_3990_);
v___x_4209_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4197_, v___x_4208_);
v___x_4210_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4209_);
v___x_4211_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4210_, v___x_3916_);
v___x_4212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__206));
v___x_4213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__208));
v___x_4214_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__210);
v___x_4215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__211));
v___x_4216_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4215_, v_currMacroScope_3892_);
v___x_4217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4217_, 0, v___x_3913_);
lean_ctor_set(v___x_4217_, 1, v___x_4214_);
lean_ctor_set(v___x_4217_, 2, v___x_4216_);
lean_ctor_set(v___x_4217_, 3, v___x_3930_);
v___x_4218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__213);
v___x_4219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__214));
v___x_4220_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4219_, v_currMacroScope_3892_);
v___x_4221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__219));
v___x_4222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4222_, 0, v___x_3913_);
lean_ctor_set(v___x_4222_, 1, v___x_4218_);
lean_ctor_set(v___x_4222_, 2, v___x_4220_);
lean_ctor_set(v___x_4222_, 3, v___x_4221_);
v___x_4223_ = l_Lean_Syntax_node3(v___x_3913_, v___x_3900_, v___x_4076_, v___x_3990_, v___x_4096_);
v___x_4224_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4222_, v___x_4223_);
v___x_4225_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4224_);
lean_inc_ref(v___x_4217_);
v___x_4226_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4213_, v___x_4217_, v___x_3916_, v___x_4153_, v___x_4225_);
v___x_4227_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4212_, v___x_4067_, v___x_3916_, v___x_4069_, v___x_4226_);
v___x_4228_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4227_, v___x_3916_);
v___x_4229_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__221);
v___x_4230_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__223));
v___x_4231_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4230_, v_currMacroScope_3892_);
v___x_4232_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4232_, 0, v___x_3913_);
lean_ctor_set(v___x_4232_, 1, v___x_4229_);
lean_ctor_set(v___x_4232_, 2, v___x_4231_);
lean_ctor_set(v___x_4232_, 3, v___x_3930_);
v___x_4233_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4129_, v___x_3916_, v___x_4232_);
v___x_4234_ = l_Lean_Syntax_node6(v___x_3913_, v___x_4126_, v___x_4128_, v___x_4233_, v___x_4136_, v___x_4144_, v___x_3916_, v___x_3916_);
v___x_4235_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4234_, v___x_3916_);
v___x_4236_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__225);
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__227));
v___x_4238_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4237_, v_currMacroScope_3892_);
v___x_4239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4239_, 0, v___x_3913_);
lean_ctor_set(v___x_4239_, 1, v___x_4236_);
lean_ctor_set(v___x_4239_, 2, v___x_4238_);
lean_ctor_set(v___x_4239_, 3, v___x_3930_);
v___x_4240_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4129_, v___x_3916_, v___x_4239_);
v___x_4241_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__228));
v___x_4242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_3913_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4177_, v___x_4242_);
v___x_4244_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4176_, v___x_4243_);
v___x_4245_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4173_, v___x_4175_, v___x_4244_);
v___x_4246_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4170_, v___x_4172_, v___x_4245_);
v___x_4247_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4246_);
v___x_4248_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4247_, v___x_3916_);
v___x_4249_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4248_);
v___x_4250_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4249_);
v___x_4251_ = l_Lean_Syntax_node6(v___x_3913_, v___x_4126_, v___x_4128_, v___x_4240_, v___x_4136_, v___x_4250_, v___x_3916_, v___x_3916_);
v___x_4252_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4251_, v___x_3916_);
v___x_4253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__230));
v___x_4254_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__231));
v___x_4255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_3913_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__233);
v___x_4257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__234));
v___x_4258_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4257_, v_currMacroScope_3892_);
v___x_4259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4259_, 0, v___x_3913_);
lean_ctor_set(v___x_4259_, 1, v___x_4256_);
lean_ctor_set(v___x_4259_, 2, v___x_4258_);
lean_ctor_set(v___x_4259_, 3, v___x_3930_);
v___x_4260_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4217_);
lean_inc(v___x_4260_);
v___x_4261_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4024_, v___x_4260_);
v___x_4262_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4261_);
lean_inc_ref(v___x_4259_);
v___x_4263_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4213_, v___x_4259_, v___x_3916_, v___x_4153_, v___x_4262_);
v___x_4264_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4212_, v___x_4067_, v___x_3916_, v___x_4069_, v___x_4263_);
v___x_4265_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4264_, v___x_3916_);
v___x_4266_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4259_);
v___x_4267_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4137_, v___x_4139_, v___x_4266_);
v___x_4268_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4267_, v___x_3916_);
v___x_4269_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_4265_, v___x_4268_);
v___x_4270_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4269_);
v___x_4271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__236));
v___x_4272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__237));
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_3913_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__239);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__240));
v___x_4276_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4275_, v_currMacroScope_3892_);
v___x_4277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4277_, 0, v___x_3913_);
lean_ctor_set(v___x_4277_, 1, v___x_4274_);
lean_ctor_set(v___x_4277_, 2, v___x_4276_);
lean_ctor_set(v___x_4277_, 3, v___x_3930_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__241));
v___x_4279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_3913_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__243);
v___x_4281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__244));
v___x_4282_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4281_, v_currMacroScope_3892_);
v___x_4283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4283_, 0, v___x_3913_);
lean_ctor_set(v___x_4283_, 1, v___x_4280_);
lean_ctor_set(v___x_4283_, 2, v___x_4282_);
lean_ctor_set(v___x_4283_, 3, v___x_3930_);
lean_inc_ref_n(v___x_4283_, 2);
v___x_4284_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4072_, v___x_4283_);
v___x_4285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__245));
v___x_4286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_3913_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4177_, v___x_4286_);
v___x_4288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__247);
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__248));
v___x_4290_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4289_, v_currMacroScope_3892_);
v___x_4291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__251));
v___x_4292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4292_, 0, v___x_3913_);
lean_ctor_set(v___x_4292_, 1, v___x_4288_);
lean_ctor_set(v___x_4292_, 2, v___x_4290_);
lean_ctor_set(v___x_4292_, 3, v___x_4291_);
v___x_4293_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4292_, v___x_4260_);
v___x_4294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__252));
v___x_4295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_3913_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4177_, v___x_4295_);
v___x_4297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__254);
v___x_4298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__256));
v___x_4299_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4298_, v_currMacroScope_3892_);
v___x_4300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4300_, 0, v___x_3913_);
lean_ctor_set(v___x_4300_, 1, v___x_4297_);
lean_ctor_set(v___x_4300_, 2, v___x_4299_);
lean_ctor_set(v___x_4300_, 3, v___x_3930_);
v___x_4301_ = l_Lean_Syntax_node5(v___x_3913_, v___x_4176_, v___x_4287_, v___x_4293_, v___x_4296_, v___x_4300_, v___x_4183_);
v___x_4302_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4173_, v___x_4175_, v___x_4301_);
v___x_4303_ = l_Lean_Syntax_node5(v___x_3913_, v___x_4071_, v___x_4284_, v___x_3916_, v___x_3916_, v___x_3967_, v___x_4302_);
v___x_4304_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4070_, v___x_4303_);
v___x_4305_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4065_, v___x_4067_, v___x_3916_, v___x_4069_, v___x_4304_);
v___x_4306_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4305_, v___x_3916_);
v___x_4307_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__257);
v___x_4308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__258));
v___x_4309_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4308_, v_currMacroScope_3892_);
v___x_4310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__260));
v___x_4311_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4311_, 0, v___x_3913_);
lean_ctor_set(v___x_4311_, 1, v___x_4307_);
lean_ctor_set(v___x_4311_, 2, v___x_4309_);
lean_ctor_set(v___x_4311_, 3, v___x_4310_);
v___x_4312_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4129_, v___x_3916_, v___x_4311_);
v___x_4313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__262);
v___x_4314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__263));
v___x_4315_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_4314_, v_currMacroScope_3892_);
v___x_4316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__266));
v___x_4317_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4317_, 0, v___x_3913_);
lean_ctor_set(v___x_4317_, 1, v___x_4313_);
lean_ctor_set(v___x_4317_, 2, v___x_4315_);
lean_ctor_set(v___x_4317_, 3, v___x_4316_);
v___x_4318_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4283_);
v___x_4319_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4317_, v___x_4318_);
v___x_4320_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4319_);
v___x_4321_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4320_, v___x_3916_);
v___x_4322_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_4321_, v___x_4142_);
v___x_4323_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4322_);
v___x_4324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__267));
v___x_4325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_3913_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v___x_4326_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4170_, v___x_4172_, v___x_4283_);
v___x_4327_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4327_, v___x_3916_);
v___x_4329_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4328_);
v___x_4330_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4329_);
v___x_4331_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_4325_, v___x_4330_);
v___x_4332_ = l_Lean_Syntax_node6(v___x_3913_, v___x_4126_, v___x_4128_, v___x_4312_, v___x_4136_, v___x_4323_, v___x_3916_, v___x_4331_);
v___x_4333_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4332_, v___x_3916_);
v___x_4334_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_4306_, v___x_4333_);
v___x_4335_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4334_);
v___x_4336_ = l_Lean_Syntax_node5(v___x_3913_, v___x_4271_, v___x_4273_, v___x_4277_, v___x_3916_, v___x_4279_, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4336_);
v___x_4338_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4253_, v___x_4255_, v___x_4270_, v___x_4337_, v___x_3916_);
v___x_4339_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4338_, v___x_3916_);
v___x_4340_ = l_Lean_Syntax_node8(v___x_3913_, v___x_3900_, v___x_4125_, v___x_4146_, v___x_4192_, v___x_4211_, v___x_4228_, v___x_4235_, v___x_4252_, v___x_4339_);
v___x_4341_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4340_);
v___x_4342_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4061_, v___x_4062_, v___x_4341_);
v___x_4343_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3900_, v___x_4046_, v___x_4342_);
v___x_4344_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v___x_4092_, v___x_4343_);
v___x_4345_ = l_Lean_Syntax_node5(v___x_3913_, v___x_4071_, v___x_4087_, v___x_3916_, v___x_3963_, v___x_3967_, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4070_, v___x_4345_);
v___x_4347_ = l_Lean_Syntax_node4(v___x_3913_, v___x_4065_, v___x_4067_, v___x_3916_, v___x_4069_, v___x_4346_);
v___x_4348_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4347_, v___x_3916_);
v___x_4349_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4154_, v___x_4086_);
v___x_4350_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4064_, v___x_4349_, v___x_3916_);
v___x_4351_ = l_Lean_Syntax_node3(v___x_3913_, v___x_3900_, v___x_4081_, v___x_4348_, v___x_4350_);
v___x_4352_ = l_Lean_Syntax_node1(v___x_3913_, v___x_4063_, v___x_4351_);
v___x_4353_ = l_Lean_Syntax_node2(v___x_3913_, v___x_4061_, v___x_4062_, v___x_4352_);
v___x_4354_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3900_, v___x_4353_);
v___x_4355_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3954_, v_adapt_3887_, v___x_4354_);
v___x_4356_ = l_Lean_Syntax_node4(v___x_3913_, v___x_3965_, v___x_3967_, v___x_4355_, v___x_3994_, v___x_3916_);
v___x_4357_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3923_, v___x_3925_, v___x_4041_, v___x_4059_, v___x_4356_, v___x_3916_);
v___x_4358_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3914_, v___x_4034_, v___x_4357_);
v___x_4359_ = l_Lean_Syntax_node3(v___x_3913_, v___x_3900_, v___x_3997_, v___x_4029_, v___x_4358_);
v___x_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
lean_ctor_set(v___x_4360_, 1, v_a_3890_);
return v___x_4360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___boxed(lean_object* v_doc_x3f_4364_, lean_object* v_elabName_4365_, lean_object* v_type_4366_, lean_object* v_monadName_4367_, lean_object* v_adapt_4368_, lean_object* v_recover_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v_doc_x3f_4364_, v_elabName_4365_, v_type_4366_, v_monadName_4367_, v_adapt_4368_, v_recover_4369_, v_a_4370_, v_a_4371_);
lean_dec_ref(v_a_4370_);
return v_res_4372_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1(void){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__0));
v___x_4417_ = l_String_toRawSubstring_x27(v___x_4416_);
return v___x_4417_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__8));
v___x_4437_ = l_Lean_mkCIdent(v___x_4436_);
return v___x_4437_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__11));
v___x_4442_ = l_Lean_mkCIdent(v___x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(lean_object* v_x_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4446_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
lean_inc(v_x_4443_);
v___x_4447_ = l_Lean_Syntax_isOfKind(v_x_4443_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec(v_x_4443_);
v___x_4448_ = lean_box(1);
v___x_4449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
lean_ctor_set(v___x_4449_, 1, v_a_4445_);
return v___x_4449_;
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v_elabName_4453_; lean_object* v___x_4454_; lean_object* v_type_4455_; lean_object* v___y_4457_; lean_object* v___x_4510_; 
v___x_4450_ = lean_unsigned_to_nat(0u);
v___x_4451_ = l_Lean_Syntax_getArg(v_x_4443_, v___x_4450_);
v___x_4452_ = lean_unsigned_to_nat(2u);
v_elabName_4453_ = l_Lean_Syntax_getArg(v_x_4443_, v___x_4452_);
v___x_4454_ = lean_unsigned_to_nat(3u);
v_type_4455_ = l_Lean_Syntax_getArg(v_x_4443_, v___x_4454_);
lean_dec(v_x_4443_);
v___x_4510_ = l_Lean_Syntax_getOptional_x3f(v___x_4451_);
lean_dec(v___x_4451_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v___x_4511_; 
v___x_4511_ = lean_box(0);
v___y_4457_ = v___x_4511_;
goto v___jp_4456_;
}
else
{
lean_object* v_val_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_val_4512_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4510_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_val_4512_);
lean_dec(v___x_4510_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_val_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
v___y_4457_ = v___x_4517_;
goto v___jp_4456_;
}
}
}
v___jp_4456_:
{
lean_object* v_quotContext_4458_; lean_object* v_currMacroScope_4459_; lean_object* v_ref_4460_; uint8_t v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v_a_4501_; lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
v_quotContext_4458_ = lean_ctor_get(v_a_4444_, 1);
v_currMacroScope_4459_ = lean_ctor_get(v_a_4444_, 2);
v_ref_4460_ = lean_ctor_get(v_a_4444_, 5);
v___x_4461_ = 0;
v___x_4462_ = l_Lean_SourceInfo_fromRef(v_ref_4460_, v___x_4461_);
v___x_4463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__162));
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__138));
v___x_4465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__3));
v___x_4466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__4));
lean_inc_n(v___x_4462_, 12);
v___x_4467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4462_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__6));
v___x_4469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__7);
v___x_4470_ = lean_box(0);
lean_inc_n(v_currMacroScope_4459_, 3);
lean_inc_n(v_quotContext_4458_, 3);
v___x_4471_ = l_Lean_addMacroScope(v_quotContext_4458_, v___x_4470_, v_currMacroScope_4459_);
v___x_4472_ = lean_box(0);
v___x_4473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__25));
v___x_4474_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4462_);
lean_ctor_set(v___x_4474_, 1, v___x_4469_);
lean_ctor_set(v___x_4474_, 2, v___x_4471_);
lean_ctor_set(v___x_4474_, 3, v___x_4473_);
v___x_4475_ = l_Lean_Syntax_node1(v___x_4462_, v___x_4468_, v___x_4474_);
v___x_4476_ = l_Lean_Syntax_node2(v___x_4462_, v___x_4465_, v___x_4467_, v___x_4475_);
v___x_4477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__164));
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__165));
v___x_4479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4462_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
v___x_4480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__167));
v___x_4481_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__1);
v___x_4482_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__2));
v___x_4483_ = l_Lean_addMacroScope(v_quotContext_4458_, v___x_4482_, v_currMacroScope_4459_);
v___x_4484_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__6));
v___x_4485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4462_);
lean_ctor_set(v___x_4485_, 1, v___x_4481_);
lean_ctor_set(v___x_4485_, 2, v___x_4483_);
lean_ctor_set(v___x_4485_, 3, v___x_4484_);
v___x_4486_ = l_Lean_Syntax_node1(v___x_4462_, v___x_4480_, v___x_4485_);
v___x_4487_ = l_Lean_Syntax_node2(v___x_4462_, v___x_4477_, v___x_4479_, v___x_4486_);
v___x_4488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabConfig_spec__4___lam__2___closed__26));
v___x_4489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4462_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = l_Lean_Syntax_node3(v___x_4462_, v___x_4464_, v___x_4476_, v___x_4487_, v___x_4489_);
v___x_4491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__53));
v___x_4492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4462_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__115);
v___x_4494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator___closed__116));
v___x_4495_ = l_Lean_addMacroScope(v_quotContext_4458_, v___x_4494_, v_currMacroScope_4459_);
v___x_4496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4462_);
lean_ctor_set(v___x_4496_, 1, v___x_4493_);
lean_ctor_set(v___x_4496_, 2, v___x_4495_);
lean_ctor_set(v___x_4496_, 3, v___x_4472_);
v___x_4497_ = l_Lean_Syntax_node3(v___x_4462_, v___x_4463_, v___x_4490_, v___x_4492_, v___x_4496_);
v___x_4498_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__9);
v___x_4499_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___closed__12);
v___x_4500_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4457_, v_elabName_4453_, v_type_4455_, v___x_4498_, v___x_4499_, v___x_4497_, v_a_4444_, v_a_4445_);
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
v_a_4502_ = lean_ctor_get(v___x_4500_, 1);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4500_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_inc(v_a_4501_);
lean_dec(v___x_4500_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4501_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1___boxed(lean_object* v_x_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__configElab__1(v_x_4520_, v_a_4521_, v_a_4522_);
lean_dec_ref(v_a_4521_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4530_ = lean_unsigned_to_nat(2u);
v___x_4531_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4529_, v___x_4530_, v_a_4525_, v_a_4526_, v_a_4527_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed(lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab(v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
return v_res_4536_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___boxed), 4, 0);
v___x_4538_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4538_, 0, v___x_4537_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1(){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = ((lean_object*)(l_Lean_Elab_Tactic_configElab___closed__1));
v___x_4541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___closed__0);
v___x_4542_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4540_, v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1___boxed(lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab__1();
return v_res_4544_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2(void){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4577_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__1));
v___x_4578_ = l_Lean_mkCIdent(v___x_4577_);
return v___x_4578_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5(void){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = ((lean_object*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__4));
v___x_4586_ = l_Lean_mkCIdent(v___x_4585_);
return v___x_4586_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_mkConfigItemViews_spec__0___closed__18));
v___x_4588_ = l_Lean_mkCIdent(v___x_4587_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(lean_object* v_x_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
lean_inc(v_x_4589_);
v___x_4593_ = l_Lean_Syntax_isOfKind(v_x_4589_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
lean_dec(v_x_4589_);
v___x_4594_ = lean_box(1);
v___x_4595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
lean_ctor_set(v___x_4595_, 1, v_a_4591_);
return v___x_4595_;
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v_elabName_4599_; lean_object* v___x_4600_; lean_object* v_type_4601_; lean_object* v___y_4603_; lean_object* v___x_4617_; 
v___x_4596_ = lean_unsigned_to_nat(0u);
v___x_4597_ = l_Lean_Syntax_getArg(v_x_4589_, v___x_4596_);
v___x_4598_ = lean_unsigned_to_nat(2u);
v_elabName_4599_ = l_Lean_Syntax_getArg(v_x_4589_, v___x_4598_);
v___x_4600_ = lean_unsigned_to_nat(3u);
v_type_4601_ = l_Lean_Syntax_getArg(v_x_4589_, v___x_4600_);
lean_dec(v_x_4589_);
v___x_4617_ = l_Lean_Syntax_getOptional_x3f(v___x_4597_);
lean_dec(v___x_4597_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v___x_4618_; 
v___x_4618_ = lean_box(0);
v___y_4603_ = v___x_4618_;
goto v___jp_4602_;
}
else
{
lean_object* v_val_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
v_val_4619_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4617_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_val_4619_);
lean_dec(v___x_4617_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_val_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
v___y_4603_ = v___x_4624_;
goto v___jp_4602_;
}
}
}
v___jp_4602_:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v_a_4608_; lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
v___x_4604_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__2);
v___x_4605_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__5);
v___x_4606_ = lean_obj_once(&l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6, &l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6_once, _init_l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___closed__6);
v___x_4607_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigElaborator(v___y_4603_, v_elabName_4599_, v_type_4601_, v___x_4604_, v___x_4605_, v___x_4606_, v_a_4590_, v_a_4591_);
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
v_a_4609_ = lean_ctor_get(v___x_4607_, 1);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4607_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_inc(v_a_4608_);
lean_dec(v___x_4607_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4608_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1___boxed(lean_object* v_x_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Config______macroRules__Lean__Elab__Tactic__commandConfigElab__1(v_x_4627_, v_a_4628_, v_a_4629_);
lean_dec_ref(v_a_4628_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkConfigElab___closed__0));
v___x_4636_ = lean_unsigned_to_nat(2u);
v___x_4637_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4635_, v___x_4636_, v_a_4631_, v_a_4632_, v_a_4633_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed(lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab(v_a_4638_, v_a_4639_, v_a_4640_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
return v_res_4642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___boxed), 4, 0);
v___x_4644_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4644_, 0, v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = ((lean_object*)(l_Lean_Elab_Tactic_commandConfigElab___closed__1));
v___x_4647_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___closed__0);
v___x_4648_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4646_, v___x_4647_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1___boxed(lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab___regBuiltin___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_checkCommandConfigElab__1();
return v_res_4650_;
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
