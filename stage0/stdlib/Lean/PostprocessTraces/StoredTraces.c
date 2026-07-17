// Lean compiler output
// Module: Lean.PostprocessTraces.StoredTraces
// Imports: public meta import Lean.PostprocessTraces.Basic public meta import Lean.Elab.Command import Lean.CoreM
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_addAndCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_docStringExt;
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Message_isTrace(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_traceContainer_x3f(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostprocessTraces"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "storeTracesAsCmd"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__2 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__2_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 198, 145, 81, 140, 195, 110, 227)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__4 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__4_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "store_traces_as "};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__6 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__6_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__6_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__7 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__7_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__8 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__8_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__9 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__9_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__9_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__10 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__10_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__7_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__10_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__11 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__11_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " in"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__12 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__12_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__12_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__13 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__13_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__11_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__13_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__14 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__14_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__15 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__15_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__16 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__16_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__16_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__17 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__17_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__14_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__17_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__18 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__18_value;
static const lean_string_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__19 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__19_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__19_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__20 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__20_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__21 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__21_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__18_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__21_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__22 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__22_value;
static const lean_ctor_object l_Lean_PostprocessTraces_storeTracesAsCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__22_value)}};
static const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd___closed__23 = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_storeTracesAsCmd = (const lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__23_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "postprocessStoredTracesCmd"};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__0_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 232, 148, 233, 198, 180, 134, 53)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "#postprocess_traces "};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__2 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__2_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__2_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__3 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__3_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__3_value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__10_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__4 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__4_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__5 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__5_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__6 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__6_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__6_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__7 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__7_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__4_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__7_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__8 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__8_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__9 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__9_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__10 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__10_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__11 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__11_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__8_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__11_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__12 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__12_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__12_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__13 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_postprocessStoredTracesCmd = (const lean_object*)&l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__13_value;
static const lean_array_object l_Lean_PostprocessTraces_instInhabitedStoredTrace_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PostprocessTraces_instInhabitedStoredTrace_default___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedStoredTrace_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_instInhabitedStoredTrace_default = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedStoredTrace_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_instInhabitedStoredTrace = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedStoredTrace_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___lam__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___lam__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___lam__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_allStoredTraces(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PostprocessTraces_findStoredTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "trace data for `"};
static const lean_object* l_Lean_PostprocessTraces_findStoredTrace___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_findStoredTrace___closed__0_value;
static lean_once_cell_t l_Lean_PostprocessTraces_findStoredTrace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_findStoredTrace___closed__1;
static const lean_string_object l_Lean_PostprocessTraces_findStoredTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "` is not available in this context (stored traces are kept in memory and are only available in the file that stored them)"};
static const lean_object* l_Lean_PostprocessTraces_findStoredTrace___closed__2 = (const lean_object*)&l_Lean_PostprocessTraces_findStoredTrace___closed__2_value;
static lean_once_cell_t l_Lean_PostprocessTraces_findStoredTrace___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_findStoredTrace___closed__3;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_storeTraces___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___closed__0;
static lean_once_cell_t l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___closed__1;
static lean_once_cell_t l_Lean_PostprocessTraces_storeTraces___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_PostprocessTraces_StoredTrace_trees___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PostprocessTraces_StoredTrace_trees___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_StoredTrace_trees___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0 = (const lean_object*)&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1;
static const lean_string_object l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2 = (const lean_object*)&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Core"};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__0 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__0_value;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "CoreM"};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__1 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__1_value;
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 126, 120, 188, 150, 235, 117, 203)}};
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 114, 191, 177, 45, 189, 121, 141)}};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2_value;
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "StoredTrace"};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__4 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__4_value;
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 162, 213, 104, 244, 174, 40, 67)}};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5_value;
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6;
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "findStoredTrace"};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__8 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__8_value;
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__8_value),LEAN_SCALAR_PTR_LITERAL(189, 237, 199, 37, 181, 117, 224, 209)}};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9_value;
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "A trace stored by `store_traces_as` (`"};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11_value;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`); inspect it with `#trace_roots "};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12_value;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` and `#postprocess_traces "};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13_value;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 64, .m_data = " <postprocessor>`, or in metaprograms, e.g. `#eval do return (← "};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14_value;
static const lean_string_object l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ").roots.size`."};
static const lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unknown stored trace `"};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "` ("};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "); store one using `store_traces_as "};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " in <command>`"};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "stored traces: "};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__10 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__10_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__10_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "no traces have been stored in this file"};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13 = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___lam__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_(lean_object* v___x_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___lam__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2____boxed(lean_object* v___x_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___lam__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_(v___x_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___f_103_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_));
v___x_104_ = lean_box(0);
v___x_105_ = lean_box(2);
v___x_106_ = l_Lean_registerEnvExtension___redArg(v___f_103_, v___x_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2____boxed(lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_();
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace_x3f(lean_object* v_env_109_, lean_object* v_declName_110_){
_start:
{
lean_object* v___x_111_; lean_object* v_asyncMode_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_111_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_112_ = lean_ctor_get(v___x_111_, 2);
v___x_113_ = lean_box(1);
v___x_114_ = lean_box(0);
v___x_115_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_113_, v___x_111_, v_env_109_, v_asyncMode_112_, v___x_114_);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_115_, v_declName_110_);
lean_dec(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace_x3f___boxed(lean_object* v_env_117_, lean_object* v_declName_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_117_, v_declName_118_);
lean_dec(v_declName_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(lean_object* v_init_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v_l_124_; lean_object* v_r_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_k_122_ = lean_ctor_get(v_x_121_, 1);
v_v_123_ = lean_ctor_get(v_x_121_, 2);
v_l_124_ = lean_ctor_get(v_x_121_, 3);
v_r_125_ = lean_ctor_get(v_x_121_, 4);
v___x_126_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(v_init_120_, v_r_125_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_k_122_);
lean_ctor_set(v___x_127_, 1, v_v_123_);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
v_init_120_ = v___x_128_;
v_x_121_ = v_l_124_;
goto _start;
}
else
{
return v_init_120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0___boxed(lean_object* v_init_130_, lean_object* v_x_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(v_init_130_, v_x_131_);
lean_dec(v_x_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_allStoredTraces(lean_object* v_env_133_){
_start:
{
lean_object* v___x_134_; lean_object* v_asyncMode_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_134_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_135_ = lean_ctor_get(v___x_134_, 2);
v___x_136_ = lean_box(1);
v___x_137_ = lean_box(0);
v___x_138_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_136_, v___x_134_, v_env_133_, v_asyncMode_135_, v___x_137_);
v___x_139_ = lean_box(0);
v___x_140_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(v___x_139_, v___x_138_);
lean_dec(v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_141_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
lean_ctor_set(v___x_146_, 4, v___x_144_);
lean_ctor_set(v___x_146_, 5, v___x_144_);
lean_ctor_set(v___x_146_, 6, v___x_144_);
lean_ctor_set(v___x_146_, 7, v___x_144_);
lean_ctor_set(v___x_146_, 8, v___x_144_);
lean_ctor_set(v___x_146_, 9, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(32u);
v___x_148_ = lean_mk_empty_array_with_capacity(v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_150_ = ((size_t)5ULL);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3);
v___x_155_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_151_);
lean_ctor_set(v___x_155_, 3, v___x_151_);
lean_ctor_set_usize(v___x_155_, 4, v___x_150_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_box(1);
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(lean_object* v_msgData_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v_options_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_165_);
lean_dec(v___x_164_);
v_options_166_ = lean_ctor_get(v___y_161_, 2);
v___x_167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_166_);
v___x_169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_169_, 0, v_env_165_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_168_);
lean_ctor_set(v___x_169_, 3, v_options_166_);
v___x_170_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_msgData_160_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___boxed(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(v_msgData_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_ref_181_; lean_object* v___x_182_; lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_ref_181_ = lean_ctor_get(v___y_178_, 5);
v___x_182_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(v_msg_177_, v___y_178_, v___y_179_);
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_inc(v_ref_181_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_ref_181_);
lean_ctor_set(v___x_187_, 1, v_a_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 1);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg___boxed(lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v_msg_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_196_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_findStoredTrace___closed__1(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_PostprocessTraces_findStoredTrace___closed__0));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_findStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_PostprocessTraces_findStoredTrace___closed__2));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace(lean_object* v_declName_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_env_208_; lean_object* v___x_209_; 
v___x_207_ = lean_st_ref_get(v_a_205_);
v_env_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_env_208_);
lean_dec(v___x_207_);
v___x_209_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_208_, v_declName_203_);
if (lean_obj_tag(v___x_209_) == 1)
{
lean_object* v_val_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_declName_203_);
v_val_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_val_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 0);
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_val_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v___x_209_);
v___x_218_ = lean_obj_once(&l_Lean_PostprocessTraces_findStoredTrace___closed__1, &l_Lean_PostprocessTraces_findStoredTrace___closed__1_once, _init_l_Lean_PostprocessTraces_findStoredTrace___closed__1);
v___x_219_ = l_Lean_MessageData_ofName(v_declName_203_);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_obj_once(&l_Lean_PostprocessTraces_findStoredTrace___closed__3, &l_Lean_PostprocessTraces_findStoredTrace___closed__3_once, _init_l_Lean_PostprocessTraces_findStoredTrace___closed__3);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_222_, v_a_204_, v_a_205_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace___boxed(lean_object* v_declName_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_PostprocessTraces_findStoredTrace(v_declName_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(lean_object* v_00_u03b1_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v_msg_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(v_00_u03b1_235_, v_msg_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___lam__0(lean_object* v_declName_241_, lean_object* v_t_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_241_, v_t_242_, v_x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__0(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_245_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__0, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__1, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg(lean_object* v_declName_250_, lean_object* v_t_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; lean_object* v_env_255_; lean_object* v_nextMacroScope_256_; lean_object* v_ngen_257_; lean_object* v_auxDeclNGen_258_; lean_object* v_traceState_259_; lean_object* v_messages_260_; lean_object* v_infoState_261_; lean_object* v_snapshotTasks_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_278_; 
v___x_254_ = lean_st_ref_take(v_a_252_);
v_env_255_ = lean_ctor_get(v___x_254_, 0);
v_nextMacroScope_256_ = lean_ctor_get(v___x_254_, 1);
v_ngen_257_ = lean_ctor_get(v___x_254_, 2);
v_auxDeclNGen_258_ = lean_ctor_get(v___x_254_, 3);
v_traceState_259_ = lean_ctor_get(v___x_254_, 4);
v_messages_260_ = lean_ctor_get(v___x_254_, 6);
v_infoState_261_ = lean_ctor_get(v___x_254_, 7);
v_snapshotTasks_262_ = lean_ctor_get(v___x_254_, 8);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_254_, 5);
lean_dec(v_unused_279_);
v___x_264_ = v___x_254_;
v_isShared_265_ = v_isSharedCheck_278_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snapshotTasks_262_);
lean_inc(v_infoState_261_);
lean_inc(v_messages_260_);
lean_inc(v_traceState_259_);
lean_inc(v_auxDeclNGen_258_);
lean_inc(v_ngen_257_);
lean_inc(v_nextMacroScope_256_);
lean_inc(v_env_255_);
lean_dec(v___x_254_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_278_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v_asyncMode_267_; lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_266_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_267_ = lean_ctor_get(v___x_266_, 2);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_268_, 0, v_declName_250_);
lean_closure_set(v___f_268_, 1, v_t_251_);
v___x_269_ = lean_box(0);
v___x_270_ = l_Lean_EnvExtension_modifyState___redArg(v___x_266_, v_env_255_, v___f_268_, v_asyncMode_267_, v___x_269_);
v___x_271_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__2, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__2_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__2);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 5, v___x_271_);
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_273_ = v___x_264_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_nextMacroScope_256_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_ngen_257_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_auxDeclNGen_258_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_traceState_259_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_277_, 6, v_messages_260_);
lean_ctor_set(v_reuseFailAlloc_277_, 7, v_infoState_261_);
lean_ctor_set(v_reuseFailAlloc_277_, 8, v_snapshotTasks_262_);
v___x_273_ = v_reuseFailAlloc_277_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_st_ref_set(v_a_252_, v___x_273_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___boxed(lean_object* v_declName_280_, lean_object* v_t_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_PostprocessTraces_storeTraces___redArg(v_declName_280_, v_t_281_, v_a_282_);
lean_dec(v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces(lean_object* v_declName_285_, lean_object* v_t_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_PostprocessTraces_storeTraces___redArg(v_declName_285_, v_t_286_, v_a_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___boxed(lean_object* v_declName_291_, lean_object* v_t_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_PostprocessTraces_storeTraces(v_declName_291_, v_t_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(size_t v_sz_297_, size_t v_i_298_, lean_object* v_bs_299_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = lean_usize_dec_lt(v_i_298_, v_sz_297_);
if (v___x_300_ == 0)
{
return v_bs_299_;
}
else
{
lean_object* v_v_301_; lean_object* v___x_302_; lean_object* v_bs_x27_303_; lean_object* v___x_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
v_v_301_ = lean_array_uget(v_bs_299_, v_i_298_);
v___x_302_ = lean_unsigned_to_nat(0u);
v_bs_x27_303_ = lean_array_uset(v_bs_299_, v_i_298_, v___x_302_);
v___x_304_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_301_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_298_, v___x_305_);
v___x_307_ = lean_array_uset(v_bs_x27_303_, v_i_298_, v___x_304_);
v_i_298_ = v___x_306_;
v_bs_299_ = v___x_307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0___boxed(lean_object* v_sz_309_, lean_object* v_i_310_, lean_object* v_bs_311_){
_start:
{
size_t v_sz_boxed_312_; size_t v_i_boxed_313_; lean_object* v_res_314_; 
v_sz_boxed_312_ = lean_unbox_usize(v_sz_309_);
lean_dec(v_sz_309_);
v_i_boxed_313_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(v_sz_boxed_312_, v_i_boxed_313_, v_bs_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(lean_object* v_as_317_, size_t v_i_318_, size_t v_stop_319_, lean_object* v_b_320_){
_start:
{
lean_object* v___y_322_; uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_eq(v_i_318_, v_stop_319_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v_data_328_; lean_object* v___x_329_; 
v___x_327_ = lean_array_uget_borrowed(v_as_317_, v_i_318_);
v_data_328_ = lean_ctor_get(v___x_327_, 4);
lean_inc(v_data_328_);
v___x_329_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___closed__0));
v___x_331_ = l_Array_append___redArg(v_b_320_, v___x_330_);
v___y_322_ = v___x_331_;
goto v___jp_321_;
}
else
{
lean_object* v_val_332_; lean_object* v_snd_333_; size_t v_sz_334_; size_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_val_332_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_329_, 1);
v_snd_333_ = lean_ctor_get(v_val_332_, 1);
lean_inc(v_snd_333_);
lean_dec(v_val_332_);
v_sz_334_ = lean_array_size(v_snd_333_);
v___x_335_ = ((size_t)0ULL);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(v_sz_334_, v___x_335_, v_snd_333_);
v___x_337_ = l_Array_append___redArg(v_b_320_, v___x_336_);
lean_dec_ref(v___x_336_);
v___y_322_ = v___x_337_;
goto v___jp_321_;
}
}
else
{
return v_b_320_;
}
v___jp_321_:
{
size_t v___x_323_; size_t v___x_324_; 
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_318_, v___x_323_);
v_i_318_ = v___x_324_;
v_b_320_ = v___y_322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___boxed(lean_object* v_as_338_, lean_object* v_i_339_, lean_object* v_stop_340_, lean_object* v_b_341_){
_start:
{
size_t v_i_boxed_342_; size_t v_stop_boxed_343_; lean_object* v_res_344_; 
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_stop_boxed_343_ = lean_unbox_usize(v_stop_340_);
lean_dec(v_stop_340_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_as_338_, v_i_boxed_342_, v_stop_boxed_343_, v_b_341_);
lean_dec_ref(v_as_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees(lean_object* v_t_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = ((lean_object*)(l_Lean_PostprocessTraces_StoredTrace_trees___closed__0));
v___x_350_ = lean_array_get_size(v_t_347_);
v___x_351_ = lean_nat_dec_lt(v___x_348_, v___x_350_);
if (v___x_351_ == 0)
{
return v___x_349_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_le(v___x_350_, v___x_350_);
if (v___x_352_ == 0)
{
if (v___x_351_ == 0)
{
return v___x_349_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_350_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_t_347_, v___x_353_, v___x_354_, v___x_349_);
return v___x_355_;
}
}
else
{
size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((size_t)0ULL);
v___x_357_ = lean_usize_of_nat(v___x_350_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_t_347_, v___x_356_, v___x_357_, v___x_349_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees___boxed(lean_object* v_t_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_PostprocessTraces_StoredTrace_trees(v_t_359_);
lean_dec_ref(v_t_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(lean_object* v_post_361_, lean_object* v_as_362_, size_t v_i_363_, size_t v_stop_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_eq(v_i_363_, v_stop_364_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_array_uget_borrowed(v_as_362_, v_i_363_);
lean_inc(v___x_370_);
lean_inc_ref(v_post_361_);
v___x_371_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_361_, v___x_370_, v___y_366_, v___y_367_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v_a_374_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
if (lean_obj_tag(v_a_372_) == 0)
{
v_a_374_ = v_b_365_;
goto v___jp_373_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_379_; 
v_val_378_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_val_378_);
lean_dec_ref_known(v_a_372_, 1);
v___x_379_ = lean_array_push(v_b_365_, v_val_378_);
v_a_374_ = v___x_379_;
goto v___jp_373_;
}
v___jp_373_:
{
size_t v___x_375_; size_t v___x_376_; 
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_363_, v___x_375_);
v_i_363_ = v___x_376_;
v_b_365_ = v_a_374_;
goto _start;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_b_365_);
lean_dec_ref(v_post_361_);
v_a_380_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_371_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_371_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec_ref(v_post_361_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_b_365_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0___boxed(lean_object* v_post_389_, lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_, lean_object* v_b_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
size_t v_i_boxed_397_; size_t v_stop_boxed_398_; lean_object* v_res_399_; 
v_i_boxed_397_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_398_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_389_, v_as_390_, v_i_boxed_397_, v_stop_boxed_398_, v_b_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_as_390_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(lean_object* v_post_402_, lean_object* v_as_403_, lean_object* v_start_404_, lean_object* v_stop_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_410_ = lean_nat_dec_lt(v_start_404_, v_stop_405_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_post_402_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_array_get_size(v_as_403_);
v___x_413_ = lean_nat_dec_le(v_stop_405_, v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_lt(v_start_404_, v___x_412_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec_ref(v_post_402_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_409_);
return v___x_415_;
}
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_usize_of_nat(v_start_404_);
v___x_417_ = lean_usize_of_nat(v___x_412_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_402_, v_as_403_, v___x_416_, v___x_417_, v___x_409_, v___y_406_, v___y_407_);
return v___x_418_;
}
}
else
{
size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_usize_of_nat(v_start_404_);
v___x_420_ = lean_usize_of_nat(v_stop_405_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_402_, v_as_403_, v___x_419_, v___x_420_, v___x_409_, v___y_406_, v___y_407_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___boxed(lean_object* v_post_422_, lean_object* v_as_423_, lean_object* v_start_424_, lean_object* v_stop_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(v_post_422_, v_as_423_, v_start_424_, v_stop_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_stop_425_);
lean_dec(v_start_424_);
lean_dec_ref(v_as_423_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess(lean_object* v_t_430_, lean_object* v_post_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_array_get_size(v_t_430_);
v___x_437_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(v_post_431_, v_t_430_, v___x_435_, v___x_436_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_437_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_437_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
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
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed(lean_object* v_t_454_, lean_object* v_post_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_PostprocessTraces_StoredTrace_postprocess(v_t_454_, v_post_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec_ref(v_t_454_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_box(0);
v___x_461_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg(){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___boxed(lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(lean_object* v_00_u03b1_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___boxed(lean_object* v_00_u03b1_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(v_00_u03b1_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(lean_object* v_as_478_, size_t v_i_479_, size_t v_stop_480_, lean_object* v_b_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_eq(v_i_479_, v_stop_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; size_t v___x_485_; size_t v___x_486_; 
v___x_483_ = lean_array_uget_borrowed(v_as_478_, v_i_479_);
lean_inc(v___x_483_);
v___x_484_ = l_Lean_MessageLog_add(v___x_483_, v_b_481_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_479_, v___x_485_);
v_i_479_ = v___x_486_;
v_b_481_ = v___x_484_;
goto _start;
}
else
{
return v_b_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5___boxed(lean_object* v_as_488_, lean_object* v_i_489_, lean_object* v_stop_490_, lean_object* v_b_491_){
_start:
{
size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_490_);
lean_dec(v_stop_490_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_as_488_, v_i_boxed_492_, v_stop_boxed_493_, v_b_491_);
lean_dec_ref(v_as_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_){
_start:
{
lean_object* v___y_500_; uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
v___x_506_ = l_Lean_Message_isTrace(v___x_505_);
if (v___x_506_ == 0)
{
v___y_500_ = v_b_498_;
goto v___jp_499_;
}
else
{
lean_object* v___x_507_; 
lean_inc(v___x_505_);
v___x_507_ = lean_array_push(v_b_498_, v___x_505_);
v___y_500_ = v___x_507_;
goto v___jp_499_;
}
}
else
{
return v_b_498_;
}
v___jp_499_:
{
size_t v___x_501_; size_t v___x_502_; 
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_496_, v___x_501_);
v_i_496_ = v___x_502_;
v_b_498_ = v___y_500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4___boxed(lean_object* v_as_508_, lean_object* v_i_509_, lean_object* v_stop_510_, lean_object* v_b_511_){
_start:
{
size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_510_);
lean_dec(v_stop_510_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_as_508_, v_i_boxed_512_, v_stop_boxed_513_, v_b_511_);
lean_dec_ref(v_as_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
if (lean_obj_tag(v_a_515_) == 0)
{
lean_object* v___x_517_; 
v___x_517_ = l_List_reverse___redArg(v_a_516_);
return v___x_517_;
}
else
{
lean_object* v_head_518_; lean_object* v_tail_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
v_head_518_ = lean_ctor_get(v_a_515_, 0);
v_tail_519_ = lean_ctor_get(v_a_515_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_528_ == 0)
{
v___x_521_ = v_a_515_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_tail_519_);
lean_inc(v_head_518_);
lean_dec(v_a_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_mkLevelParam(v_head_518_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_a_516_);
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_516_);
v___x_525_ = v_reuseFailAlloc_527_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v_a_515_ = v_tail_519_;
v_a_516_ = v___x_525_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__0));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__2));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__4));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__6));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__8));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(lean_object* v_msg_550_, lean_object* v_declHint_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v_env_555_; uint8_t v___x_556_; 
v___x_554_ = lean_st_ref_get(v___y_552_);
v_env_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc_ref(v_env_555_);
lean_dec(v___x_554_);
v___x_556_ = l_Lean_Name_isAnonymous(v_declHint_551_);
if (v___x_556_ == 0)
{
uint8_t v_isExporting_557_; 
v_isExporting_557_ = lean_ctor_get_uint8(v_env_555_, sizeof(void*)*8);
if (v_isExporting_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec_ref(v_env_555_);
lean_dec(v_declHint_551_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_msg_550_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; uint8_t v___x_560_; 
lean_inc_ref(v_env_555_);
v___x_559_ = l_Lean_Environment_setExporting(v_env_555_, v___x_556_);
lean_inc(v_declHint_551_);
lean_inc_ref(v___x_559_);
v___x_560_ = l_Lean_Environment_contains(v___x_559_, v_declHint_551_, v_isExporting_557_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec_ref(v___x_559_);
lean_dec_ref(v_env_555_);
lean_dec(v_declHint_551_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_msg_550_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_c_567_; lean_object* v___x_568_; 
v___x_562_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_564_ = l_Lean_Options_empty;
v___x_565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_565_, 0, v___x_559_);
lean_ctor_set(v___x_565_, 1, v___x_562_);
lean_ctor_set(v___x_565_, 2, v___x_563_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
lean_inc(v_declHint_551_);
v___x_566_ = l_Lean_MessageData_ofConstName(v_declHint_551_, v___x_556_);
v_c_567_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_567_, 0, v___x_565_);
lean_ctor_set(v_c_567_, 1, v___x_566_);
v___x_568_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_555_, v_declHint_551_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_env_555_);
lean_dec(v_declHint_551_);
v___x_569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v_c_567_);
v___x_571_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_MessageData_note(v___x_572_);
v___x_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_574_, 0, v_msg_550_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_611_; 
v_val_576_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_611_ == 0)
{
v___x_578_ = v___x_568_;
v_isShared_579_ = v_isSharedCheck_611_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v___x_568_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_611_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_mod_583_; uint8_t v___x_584_; 
v___x_580_ = lean_box(0);
v___x_581_ = l_Lean_Environment_header(v_env_555_);
lean_dec_ref(v_env_555_);
v___x_582_ = l_Lean_EnvironmentHeader_moduleNames(v___x_581_);
v_mod_583_ = lean_array_get(v___x_580_, v___x_582_, v_val_576_);
lean_dec(v_val_576_);
lean_dec_ref(v___x_582_);
v___x_584_ = l_Lean_isPrivateName(v_declHint_551_);
lean_dec(v_declHint_551_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_585_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_c_567_);
v___x_587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_MessageData_ofName(v_mod_583_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_MessageData_note(v___x_592_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v_msg_550_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 0);
lean_ctor_set(v___x_578_, 0, v___x_594_);
v___x_596_ = v___x_578_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_598_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_c_567_);
v___x_600_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_MessageData_ofName(v_mod_583_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_MessageData_note(v___x_605_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v_msg_550_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 0);
lean_ctor_set(v___x_578_, 0, v___x_607_);
v___x_609_ = v___x_578_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec_ref(v_env_555_);
lean_dec(v_declHint_551_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_msg_550_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___boxed(lean_object* v_msg_613_, lean_object* v_declHint_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_613_, v_declHint_614_, v___y_615_);
lean_dec(v___y_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(lean_object* v_msg_618_, lean_object* v_declHint_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_633_; 
v___x_623_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_618_, v_declHint_619_, v___y_621_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_633_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_unknownIdentifierMessageTag;
v___x_629_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_a_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_634_, lean_object* v_declHint_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_634_, v_declHint_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_639_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(lean_object* v_opts_640_, lean_object* v_opt_641_){
_start:
{
lean_object* v_name_642_; lean_object* v_defValue_643_; lean_object* v_map_644_; lean_object* v___x_645_; 
v_name_642_ = lean_ctor_get(v_opt_641_, 0);
v_defValue_643_ = lean_ctor_get(v_opt_641_, 1);
v_map_644_ = lean_ctor_get(v_opts_640_, 0);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_644_, v_name_642_);
if (lean_obj_tag(v___x_645_) == 0)
{
uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_defValue_643_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; 
v_val_647_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_645_, 1);
if (lean_obj_tag(v_val_647_) == 1)
{
uint8_t v_v_648_; 
v_v_648_ = lean_ctor_get_uint8(v_val_647_, 0);
lean_dec_ref_known(v_val_647_, 0);
return v_v_648_;
}
else
{
uint8_t v___x_649_; 
lean_dec(v_val_647_);
v___x_649_ = lean_unbox(v_defValue_643_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21___boxed(lean_object* v_opts_650_, lean_object* v_opt_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_650_, v_opt_651_);
lean_dec_ref(v_opt_651_);
lean_dec_ref(v_opts_650_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(1);
v___x_655_ = l_Lean_MessageData_ofFormat(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2));
v___x_660_ = l_Lean_MessageData_ofFormat(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
return v_x_661_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_686_; 
v_head_663_ = lean_ctor_get(v_x_662_, 0);
v_tail_664_ = lean_ctor_get(v_x_662_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_662_);
if (v_isSharedCheck_686_ == 0)
{
v___x_666_ = v_x_662_;
v_isShared_667_ = v_isSharedCheck_686_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_tail_664_);
lean_inc(v_head_663_);
lean_dec(v_x_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_686_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_before_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_684_; 
v_before_668_ = lean_ctor_get(v_head_663_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_head_663_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_head_663_, 1);
lean_dec(v_unused_685_);
v___x_670_ = v_head_663_;
v_isShared_671_ = v_isSharedCheck_684_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_before_668_);
lean_dec(v_head_663_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_684_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 7);
lean_ctor_set(v___x_670_, 1, v___x_672_);
lean_ctor_set(v___x_670_, 0, v_x_661_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_683_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 7);
lean_ctor_set(v___x_666_, 1, v___x_675_);
lean_ctor_set(v___x_666_, 0, v___x_674_);
v___x_677_ = v___x_666_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_MessageData_ofSyntax(v_before_668_);
v___x_679_ = l_Lean_indentD(v___x_678_);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_677_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v_x_661_ = v___x_680_;
v_x_662_ = v_tail_664_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1));
v___x_691_ = l_Lean_MessageData_ofFormat(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_msgData_692_, lean_object* v_macroStack_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; lean_object* v_scopes_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_opts_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_696_ = lean_st_ref_get(v___y_694_);
v_scopes_697_ = lean_ctor_get(v___x_696_, 2);
lean_inc(v_scopes_697_);
lean_dec(v___x_696_);
v___x_698_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_699_ = l_List_head_x21___redArg(v___x_698_, v_scopes_697_);
lean_dec(v_scopes_697_);
v_opts_700_ = lean_ctor_get(v___x_699_, 1);
lean_inc_ref(v_opts_700_);
lean_dec(v___x_699_);
v___x_701_ = l_Lean_Elab_pp_macroStack;
v___x_702_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_700_, v___x_701_);
lean_dec_ref(v_opts_700_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v_macroStack_693_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_msgData_692_);
return v___x_703_;
}
else
{
if (lean_obj_tag(v_macroStack_693_) == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v_msgData_692_);
return v___x_704_;
}
else
{
lean_object* v_head_705_; lean_object* v_after_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_721_; 
v_head_705_ = lean_ctor_get(v_macroStack_693_, 0);
lean_inc(v_head_705_);
v_after_706_ = lean_ctor_get(v_head_705_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_head_705_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_head_705_, 0);
lean_dec(v_unused_722_);
v___x_708_ = v_head_705_;
v_isShared_709_ = v_isSharedCheck_721_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_after_706_);
lean_dec(v_head_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_721_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 7);
lean_ctor_set(v___x_708_, 1, v___x_710_);
lean_ctor_set(v___x_708_, 0, v_msgData_692_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_msgData_692_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_720_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_msgData_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_713_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_MessageData_ofSyntax(v_after_706_);
v___x_716_ = l_Lean_indentD(v___x_715_);
v_msgData_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_717_, 0, v___x_714_);
lean_ctor_set(v_msgData_717_, 1, v___x_716_);
v___x_718_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(v_msgData_717_, v_macroStack_693_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_msgData_723_, lean_object* v_macroStack_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_723_, v_macroStack_724_, v___y_725_);
lean_dec(v___y_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(lean_object* v_msgData_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v_env_732_; lean_object* v___x_733_; lean_object* v_scopes_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_opts_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_731_ = lean_st_ref_get(v___y_729_);
v_env_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_env_732_);
lean_dec(v___x_731_);
v___x_733_ = lean_st_ref_get(v___y_729_);
v_scopes_734_ = lean_ctor_get(v___x_733_, 2);
lean_inc(v_scopes_734_);
lean_dec(v___x_733_);
v___x_735_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_736_ = l_List_head_x21___redArg(v___x_735_, v_scopes_734_);
lean_dec(v_scopes_734_);
v_opts_737_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_opts_737_);
lean_dec(v___x_736_);
v___x_738_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_739_ = lean_unsigned_to_nat(32u);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
lean_dec_ref(v___x_740_);
v___x_741_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_742_, 0, v_env_732_);
lean_ctor_set(v___x_742_, 1, v___x_738_);
lean_ctor_set(v___x_742_, 2, v___x_741_);
lean_ctor_set(v___x_742_, 3, v_opts_737_);
v___x_743_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_msgData_728_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg___boxed(lean_object* v_msgData_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_745_, v___y_746_);
lean_dec(v___y_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Elab_Command_getRef___redArg(v___y_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_macroStack_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v_macroStack_755_ = lean_ctor_get(v___y_750_, 4);
v___x_756_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msg_749_, v___y_751_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = l_Lean_Elab_getBetterRef(v_a_754_, v_macroStack_755_);
lean_dec(v_a_754_);
lean_inc(v_macroStack_755_);
v___x_759_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_a_757_, v_macroStack_755_, v___y_751_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_758_);
lean_ctor_set(v___x_764_, 1, v_a_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 1);
lean_ctor_set(v___x_762_, 0, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_msg_749_);
v_a_769_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_753_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_753_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object* v_ref_782_, lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Elab_Command_getRef___redArg(v___y_784_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v_fileName_789_; lean_object* v_fileMap_790_; lean_object* v_currRecDepth_791_; lean_object* v_cmdPos_792_; lean_object* v_macroStack_793_; lean_object* v_quotContext_x3f_794_; lean_object* v_currMacroScope_795_; lean_object* v_snap_x3f_796_; lean_object* v_cancelTk_x3f_797_; uint8_t v_suppressElabErrors_798_; lean_object* v_ref_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v_fileName_789_ = lean_ctor_get(v___y_784_, 0);
v_fileMap_790_ = lean_ctor_get(v___y_784_, 1);
v_currRecDepth_791_ = lean_ctor_get(v___y_784_, 2);
v_cmdPos_792_ = lean_ctor_get(v___y_784_, 3);
v_macroStack_793_ = lean_ctor_get(v___y_784_, 4);
v_quotContext_x3f_794_ = lean_ctor_get(v___y_784_, 5);
v_currMacroScope_795_ = lean_ctor_get(v___y_784_, 6);
v_snap_x3f_796_ = lean_ctor_get(v___y_784_, 8);
v_cancelTk_x3f_797_ = lean_ctor_get(v___y_784_, 9);
v_suppressElabErrors_798_ = lean_ctor_get_uint8(v___y_784_, sizeof(void*)*10);
v_ref_799_ = l_Lean_replaceRef(v_ref_782_, v_a_788_);
lean_dec(v_a_788_);
lean_inc(v_cancelTk_x3f_797_);
lean_inc(v_snap_x3f_796_);
lean_inc(v_currMacroScope_795_);
lean_inc(v_quotContext_x3f_794_);
lean_inc(v_macroStack_793_);
lean_inc(v_cmdPos_792_);
lean_inc(v_currRecDepth_791_);
lean_inc_ref(v_fileMap_790_);
lean_inc_ref(v_fileName_789_);
v___x_800_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_800_, 0, v_fileName_789_);
lean_ctor_set(v___x_800_, 1, v_fileMap_790_);
lean_ctor_set(v___x_800_, 2, v_currRecDepth_791_);
lean_ctor_set(v___x_800_, 3, v_cmdPos_792_);
lean_ctor_set(v___x_800_, 4, v_macroStack_793_);
lean_ctor_set(v___x_800_, 5, v_quotContext_x3f_794_);
lean_ctor_set(v___x_800_, 6, v_currMacroScope_795_);
lean_ctor_set(v___x_800_, 7, v_ref_799_);
lean_ctor_set(v___x_800_, 8, v_snap_x3f_796_);
lean_ctor_set(v___x_800_, 9, v_cancelTk_x3f_797_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*10, v_suppressElabErrors_798_);
v___x_801_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_783_, v___x_800_, v___y_785_);
lean_dec_ref_known(v___x_800_, 10);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_msg_783_);
v_a_802_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_787_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_787_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object* v_ref_810_, lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_810_, v_msg_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v_ref_810_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(lean_object* v_ref_816_, lean_object* v_msg_817_, lean_object* v_declHint_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_a_823_; lean_object* v___x_824_; 
v___x_822_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_817_, v_declHint_818_, v___y_819_, v___y_820_);
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_822_);
v___x_824_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_816_, v_a_823_, v___y_819_, v___y_820_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg___boxed(lean_object* v_ref_825_, lean_object* v_msg_826_, lean_object* v_declHint_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_825_, v_msg_826_, v_declHint_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_ref_825_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object* v_ref_838_, lean_object* v_constName_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_843_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1);
v___x_844_ = 0;
lean_inc(v_constName_839_);
v___x_845_ = l_Lean_MessageData_ofConstName(v_constName_839_, v___x_844_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_843_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_838_, v___x_848_, v_constName_839_, v___y_840_, v___y_841_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_ref_850_, lean_object* v_constName_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_850_, v_constName_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v_ref_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_constName_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Elab_Command_getRef___redArg(v___y_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_a_861_, v_constName_856_, v___y_857_, v___y_858_);
lean_dec(v_a_861_);
return v___x_862_;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_constName_856_);
v_a_863_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_860_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_constName_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(lean_object* v_constName_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v_env_881_; uint8_t v___x_882_; lean_object* v___x_883_; 
v___x_880_ = lean_st_ref_get(v___y_878_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_881_);
lean_dec(v___x_880_);
v___x_882_ = 0;
lean_inc(v_constName_876_);
v___x_883_ = l_Lean_Environment_findConstVal_x3f(v_env_881_, v_constName_876_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_876_, v___y_877_, v___y_878_);
return v___x_884_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_constName_876_);
v_val_885_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_883_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v___x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 0);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_val_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6___boxed(lean_object* v_constName_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(lean_object* v_constName_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
lean_inc(v_constName_898_);
v___x_902_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_914_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_914_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_levelParams_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v_levelParams_907_ = lean_ctor_get(v_a_903_, 1);
lean_inc(v_levelParams_907_);
lean_dec(v_a_903_);
v___x_908_ = lean_box(0);
v___x_909_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(v_levelParams_907_, v___x_908_);
v___x_910_ = l_Lean_mkConst(v_constName_898_, v___x_909_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_910_);
v___x_912_ = v___x_905_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_constName_898_);
v_a_915_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_902_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_902_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5___boxed(lean_object* v_constName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_constName_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(lean_object* v_t_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; lean_object* v_infoState_932_; uint8_t v_enabled_933_; 
v___x_931_ = lean_st_ref_get(v___y_929_);
v_infoState_932_ = lean_ctor_get(v___x_931_, 8);
lean_inc_ref(v_infoState_932_);
lean_dec(v___x_931_);
v_enabled_933_ = lean_ctor_get_uint8(v_infoState_932_, sizeof(void*)*3);
lean_dec_ref(v_infoState_932_);
if (v_enabled_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_t_928_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v_infoState_937_; lean_object* v_env_938_; lean_object* v_messages_939_; lean_object* v_scopes_940_; lean_object* v_usedQuotCtxts_941_; lean_object* v_nextMacroScope_942_; lean_object* v_maxRecDepth_943_; lean_object* v_ngen_944_; lean_object* v_auxDeclNGen_945_; lean_object* v_traceState_946_; lean_object* v_snapshotTasks_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_969_; 
v___x_936_ = lean_st_ref_take(v___y_929_);
v_infoState_937_ = lean_ctor_get(v___x_936_, 8);
v_env_938_ = lean_ctor_get(v___x_936_, 0);
v_messages_939_ = lean_ctor_get(v___x_936_, 1);
v_scopes_940_ = lean_ctor_get(v___x_936_, 2);
v_usedQuotCtxts_941_ = lean_ctor_get(v___x_936_, 3);
v_nextMacroScope_942_ = lean_ctor_get(v___x_936_, 4);
v_maxRecDepth_943_ = lean_ctor_get(v___x_936_, 5);
v_ngen_944_ = lean_ctor_get(v___x_936_, 6);
v_auxDeclNGen_945_ = lean_ctor_get(v___x_936_, 7);
v_traceState_946_ = lean_ctor_get(v___x_936_, 9);
v_snapshotTasks_947_ = lean_ctor_get(v___x_936_, 10);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_969_ == 0)
{
v___x_949_ = v___x_936_;
v_isShared_950_ = v_isSharedCheck_969_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_snapshotTasks_947_);
lean_inc(v_traceState_946_);
lean_inc(v_infoState_937_);
lean_inc(v_auxDeclNGen_945_);
lean_inc(v_ngen_944_);
lean_inc(v_maxRecDepth_943_);
lean_inc(v_nextMacroScope_942_);
lean_inc(v_usedQuotCtxts_941_);
lean_inc(v_scopes_940_);
lean_inc(v_messages_939_);
lean_inc(v_env_938_);
lean_dec(v___x_936_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_969_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
uint8_t v_enabled_951_; lean_object* v_assignment_952_; lean_object* v_lazyAssignment_953_; lean_object* v_trees_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_968_; 
v_enabled_951_ = lean_ctor_get_uint8(v_infoState_937_, sizeof(void*)*3);
v_assignment_952_ = lean_ctor_get(v_infoState_937_, 0);
v_lazyAssignment_953_ = lean_ctor_get(v_infoState_937_, 1);
v_trees_954_ = lean_ctor_get(v_infoState_937_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v_infoState_937_);
if (v_isSharedCheck_968_ == 0)
{
v___x_956_ = v_infoState_937_;
v_isShared_957_ = v_isSharedCheck_968_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_trees_954_);
lean_inc(v_lazyAssignment_953_);
lean_inc(v_assignment_952_);
lean_dec(v_infoState_937_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_968_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Lean_PersistentArray_push___redArg(v_trees_954_, v_t_928_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 2, v___x_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_assignment_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_lazyAssignment_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v___x_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3, v_enabled_951_);
v___x_960_ = v_reuseFailAlloc_967_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 8, v___x_960_);
v___x_962_ = v___x_949_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_env_938_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_messages_939_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_scopes_940_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_usedQuotCtxts_941_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_nextMacroScope_942_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_maxRecDepth_943_);
lean_ctor_set(v_reuseFailAlloc_966_, 6, v_ngen_944_);
lean_ctor_set(v_reuseFailAlloc_966_, 7, v_auxDeclNGen_945_);
lean_ctor_set(v_reuseFailAlloc_966_, 8, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_966_, 9, v_traceState_946_);
lean_ctor_set(v_reuseFailAlloc_966_, 10, v_snapshotTasks_947_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_st_ref_set(v___y_929_, v___x_962_);
v___x_964_ = lean_box(0);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_t_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_970_, v___y_971_);
lean_dec(v___y_971_);
return v_res_973_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(32u);
v___x_975_ = lean_mk_empty_array_with_capacity(v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1(void){
_start:
{
size_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_977_ = ((size_t)5ULL);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_unsigned_to_nat(32u);
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
v___x_981_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0);
v___x_982_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
lean_ctor_set(v___x_982_, 2, v___x_978_);
lean_ctor_set(v___x_982_, 3, v___x_978_);
lean_ctor_set_usize(v___x_982_, 4, v___x_977_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(lean_object* v_t_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_infoState_988_; uint8_t v_enabled_989_; 
v___x_987_ = lean_st_ref_get(v___y_985_);
v_infoState_988_ = lean_ctor_get(v___x_987_, 8);
lean_inc_ref(v_infoState_988_);
lean_dec(v___x_987_);
v_enabled_989_ = lean_ctor_get_uint8(v_infoState_988_, sizeof(void*)*3);
lean_dec_ref(v_infoState_988_);
if (v_enabled_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref(v_t_983_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1);
v___x_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_993_, 0, v_t_983_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v___x_993_, v___y_985_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___boxed(lean_object* v_t_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v_t_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(lean_object* v_stx_1000_, lean_object* v_n_1001_, lean_object* v_expectedType_x3f_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_n_1001_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_stx_1000_);
v___x_1010_ = l_Lean_LocalContext_empty;
v___x_1011_ = 0;
v___x_1012_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1012_, 0, v___x_1009_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
lean_ctor_set(v___x_1012_, 2, v_expectedType_x3f_1002_);
lean_ctor_set(v___x_1012_, 3, v_a_1007_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*4, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*4 + 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v___x_1013_, v___y_1003_, v___y_1004_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_expectedType_x3f_1002_);
lean_dec(v_stx_1000_);
v_a_1015_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1006_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1006_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3___boxed(lean_object* v_stx_1023_, lean_object* v_n_1024_, lean_object* v_expectedType_x3f_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_stx_1023_, v_n_1024_, v_expectedType_x3f_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1029_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(lean_object* v_declName_1036_, lean_object* v_docString_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___y_1042_; lean_object* v___x_1067_; lean_object* v_env_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_st_ref_get(v___y_1039_);
v_env_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_ref(v_env_1068_);
lean_dec(v___x_1067_);
v___x_1069_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1068_, v_declName_1036_);
lean_dec_ref(v_env_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
v___y_1042_ = v___y_1039_;
goto v___jp_1041_;
}
else
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref_known(v___x_1069_, 1);
lean_dec_ref(v_docString_1037_);
v___x_1070_ = 0;
v___x_1071_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1);
v___x_1072_ = l_Lean_MessageData_ofConstName(v_declName_1036_, v___x_1070_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_1075_, v___y_1038_, v___y_1039_);
return v___x_1076_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v_env_1044_; lean_object* v_nextMacroScope_1045_; lean_object* v_ngen_1046_; lean_object* v_auxDeclNGen_1047_; lean_object* v_traceState_1048_; lean_object* v_messages_1049_; lean_object* v_infoState_1050_; lean_object* v_snapshotTasks_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1065_; 
v___x_1043_ = lean_st_ref_take(v___y_1042_);
v_env_1044_ = lean_ctor_get(v___x_1043_, 0);
v_nextMacroScope_1045_ = lean_ctor_get(v___x_1043_, 1);
v_ngen_1046_ = lean_ctor_get(v___x_1043_, 2);
v_auxDeclNGen_1047_ = lean_ctor_get(v___x_1043_, 3);
v_traceState_1048_ = lean_ctor_get(v___x_1043_, 4);
v_messages_1049_ = lean_ctor_get(v___x_1043_, 6);
v_infoState_1050_ = lean_ctor_get(v___x_1043_, 7);
v_snapshotTasks_1051_ = lean_ctor_get(v___x_1043_, 8);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___x_1043_, 5);
lean_dec(v_unused_1066_);
v___x_1053_ = v___x_1043_;
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snapshotTasks_1051_);
lean_inc(v_infoState_1050_);
lean_inc(v_messages_1049_);
lean_inc(v_traceState_1048_);
lean_inc(v_auxDeclNGen_1047_);
lean_inc(v_ngen_1046_);
lean_inc(v_nextMacroScope_1045_);
lean_inc(v_env_1044_);
lean_dec(v___x_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1055_ = l_Lean_docStringExt;
v___x_1056_ = l_String_removeLeadingSpaces(v_docString_1037_);
v___x_1057_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1055_, v_env_1044_, v_declName_1036_, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__2, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__2_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__2);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 5, v___x_1058_);
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1060_ = v___x_1053_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_nextMacroScope_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_ngen_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_auxDeclNGen_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_traceState_1048_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_messages_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 7, v_infoState_1050_);
lean_ctor_set(v_reuseFailAlloc_1064_, 8, v_snapshotTasks_1051_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_st_ref_set(v___y_1042_, v___x_1060_);
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed(lean_object* v_declName_1077_, lean_object* v_docString_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(v_declName_1077_, v_docString_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(lean_object* v_stx_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = 0;
v___x_1087_ = l_Lean_Syntax_getRange_x3f(v_stx_1083_, v___x_1086_);
if (lean_obj_tag(v___x_1087_) == 1)
{
lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1100_; 
v_val_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1100_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1100_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_fileMap_1092_; lean_object* v_start_1093_; lean_object* v_stop_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v_fileMap_1092_ = lean_ctor_get(v___y_1084_, 1);
v_start_1093_ = lean_ctor_get(v_val_1088_, 0);
lean_inc(v_start_1093_);
v_stop_1094_ = lean_ctor_get(v_val_1088_, 1);
lean_inc(v_stop_1094_);
lean_dec(v_val_1088_);
lean_inc_ref(v_fileMap_1092_);
v___x_1095_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_1092_, v_start_1093_, v_stop_1094_);
lean_dec(v_stop_1094_);
lean_dec(v_start_1093_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1095_);
v___x_1097_ = v___x_1090_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v___x_1087_);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg___boxed(lean_object* v_stx_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1103_, v___y_1104_);
lean_dec_ref(v___y_1104_);
lean_dec(v_stx_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(lean_object* v_declName_1107_, lean_object* v_declRanges_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_Name_isAnonymous(v_declName_1107_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v_env_1113_; lean_object* v_messages_1114_; lean_object* v_scopes_1115_; lean_object* v_usedQuotCtxts_1116_; lean_object* v_nextMacroScope_1117_; lean_object* v_maxRecDepth_1118_; lean_object* v_ngen_1119_; lean_object* v_auxDeclNGen_1120_; lean_object* v_infoState_1121_; lean_object* v_traceState_1122_; lean_object* v_snapshotTasks_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1135_; 
v___x_1112_ = lean_st_ref_take(v___y_1109_);
v_env_1113_ = lean_ctor_get(v___x_1112_, 0);
v_messages_1114_ = lean_ctor_get(v___x_1112_, 1);
v_scopes_1115_ = lean_ctor_get(v___x_1112_, 2);
v_usedQuotCtxts_1116_ = lean_ctor_get(v___x_1112_, 3);
v_nextMacroScope_1117_ = lean_ctor_get(v___x_1112_, 4);
v_maxRecDepth_1118_ = lean_ctor_get(v___x_1112_, 5);
v_ngen_1119_ = lean_ctor_get(v___x_1112_, 6);
v_auxDeclNGen_1120_ = lean_ctor_get(v___x_1112_, 7);
v_infoState_1121_ = lean_ctor_get(v___x_1112_, 8);
v_traceState_1122_ = lean_ctor_get(v___x_1112_, 9);
v_snapshotTasks_1123_ = lean_ctor_get(v___x_1112_, 10);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1125_ = v___x_1112_;
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snapshotTasks_1123_);
lean_inc(v_traceState_1122_);
lean_inc(v_infoState_1121_);
lean_inc(v_auxDeclNGen_1120_);
lean_inc(v_ngen_1119_);
lean_inc(v_maxRecDepth_1118_);
lean_inc(v_nextMacroScope_1117_);
lean_inc(v_usedQuotCtxts_1116_);
lean_inc(v_scopes_1115_);
lean_inc(v_messages_1114_);
lean_inc(v_env_1113_);
lean_dec(v___x_1112_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = l_Lean_declRangeExt;
v___x_1128_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1127_, v_env_1113_, v_declName_1107_, v_declRanges_1108_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_messages_1114_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_scopes_1115_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_usedQuotCtxts_1116_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_nextMacroScope_1117_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v_maxRecDepth_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 6, v_ngen_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 7, v_auxDeclNGen_1120_);
lean_ctor_set(v_reuseFailAlloc_1134_, 8, v_infoState_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 9, v_traceState_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 10, v_snapshotTasks_1123_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_st_ref_set(v___y_1109_, v___x_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v_declRanges_1108_);
lean_dec(v_declName_1107_);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg___boxed(lean_object* v_declName_1138_, lean_object* v_declRanges_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1138_, v_declRanges_1139_, v___y_1140_);
lean_dec(v___y_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(lean_object* v_declName_1143_, lean_object* v_rangeStx_1144_, lean_object* v_selectionRangeStx_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1166_; 
v___x_1149_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_rangeStx_1144_, v___y_1146_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1166_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1166_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
if (lean_obj_tag(v_a_1150_) == 1)
{
lean_object* v_val_1154_; lean_object* v___x_1155_; lean_object* v_a_1156_; lean_object* v_a_1158_; 
lean_del_object(v___x_1152_);
v_val_1154_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v_a_1150_, 1);
v___x_1155_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_selectionRangeStx_1145_, v___y_1146_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1155_);
if (lean_obj_tag(v_a_1156_) == 0)
{
lean_inc(v_val_1154_);
v_a_1158_ = v_val_1154_;
goto v___jp_1157_;
}
else
{
lean_object* v_val_1161_; 
v_val_1161_ = lean_ctor_get(v_a_1156_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v_a_1156_, 1);
v_a_1158_ = v_val_1161_;
goto v___jp_1157_;
}
v___jp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_val_1154_);
lean_ctor_set(v___x_1159_, 1, v_a_1158_);
v___x_1160_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1143_, v___x_1159_, v___y_1147_);
return v___x_1160_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_dec(v_a_1150_);
lean_dec(v_declName_1143_);
v___x_1162_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1162_);
v___x_1164_ = v___x_1152_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2___boxed(lean_object* v_declName_1167_, lean_object* v_rangeStx_1168_, lean_object* v_selectionRangeStx_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v_declName_1167_, v_rangeStx_1168_, v_selectionRangeStx_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v_selectionRangeStx_1169_);
lean_dec(v_rangeStx_1168_);
return v_res_1173_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2));
v___x_1182_ = l_Lean_mkConst(v___x_1181_, v___x_1180_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5));
v___x_1190_ = l_Lean_mkConst(v___x_1189_, v___x_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6);
v___x_1192_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3);
v___x_1193_ = l_Lean_Expr_app___override(v___x_1192_, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9));
v___x_1201_ = l_Lean_mkConst(v___x_1200_, v___x_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3));
lean_inc(v_x_1207_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v_x_1207_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v_x_1207_);
v___x_1213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_st_ref_get(v_a_1209_);
v___x_1215_ = l_Lean_Elab_Command_getScope___redArg(v_a_1209_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = lean_unsigned_to_nat(3u);
v___x_1218_ = l_Lean_Syntax_getArg(v_x_1207_, v___x_1217_);
v___x_1219_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_1218_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v_env_1222_; lean_object* v_currNamespace_1223_; lean_object* v_env_1224_; lean_object* v_messages_1225_; lean_object* v_scopes_1226_; lean_object* v_usedQuotCtxts_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_maxRecDepth_1229_; lean_object* v_ngen_1230_; lean_object* v_auxDeclNGen_1231_; lean_object* v_infoState_1232_; lean_object* v_traceState_1233_; lean_object* v_snapshotTasks_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1318_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = lean_st_ref_take(v_a_1209_);
v_env_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_ref(v_env_1222_);
lean_dec(v___x_1214_);
v_currNamespace_1223_ = lean_ctor_get(v_a_1216_, 2);
lean_inc(v_currNamespace_1223_);
lean_dec(v_a_1216_);
v_env_1224_ = lean_ctor_get(v___x_1221_, 0);
v_messages_1225_ = lean_ctor_get(v___x_1221_, 1);
v_scopes_1226_ = lean_ctor_get(v___x_1221_, 2);
v_usedQuotCtxts_1227_ = lean_ctor_get(v___x_1221_, 3);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1221_, 4);
v_maxRecDepth_1229_ = lean_ctor_get(v___x_1221_, 5);
v_ngen_1230_ = lean_ctor_get(v___x_1221_, 6);
v_auxDeclNGen_1231_ = lean_ctor_get(v___x_1221_, 7);
v_infoState_1232_ = lean_ctor_get(v___x_1221_, 8);
v_traceState_1233_ = lean_ctor_get(v___x_1221_, 9);
v_snapshotTasks_1234_ = lean_ctor_get(v___x_1221_, 10);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1236_ = v___x_1221_;
v_isShared_1237_ = v_isSharedCheck_1318_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snapshotTasks_1234_);
lean_inc(v_traceState_1233_);
lean_inc(v_infoState_1232_);
lean_inc(v_auxDeclNGen_1231_);
lean_inc(v_ngen_1230_);
lean_inc(v_maxRecDepth_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_usedQuotCtxts_1227_);
lean_inc(v_scopes_1226_);
lean_inc(v_messages_1225_);
lean_inc(v_env_1224_);
lean_dec(v___x_1221_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1318_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_id_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___y_1246_; lean_object* v___y_1250_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_unsigned_to_nat(1u);
v_id_1240_ = l_Lean_Syntax_getArg(v_x_1207_, v___x_1239_);
lean_dec(v_x_1207_);
v___x_1241_ = lean_box(0);
v___x_1242_ = l_Lean_TSyntax_getId(v_id_1240_);
lean_inc(v___x_1242_);
v___x_1243_ = l_Lean_Name_append(v_currNamespace_1223_, v___x_1242_);
v___x_1244_ = l_Lean_mkPrivateName(v_env_1222_, v___x_1243_);
lean_dec_ref(v_env_1222_);
v___x_1309_ = lean_array_get_size(v_a_1220_);
v___x_1310_ = lean_nat_dec_lt(v___x_1238_, v___x_1309_);
if (v___x_1310_ == 0)
{
v___y_1250_ = v_messages_1225_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_le(v___x_1309_, v___x_1309_);
if (v___x_1311_ == 0)
{
if (v___x_1310_ == 0)
{
v___y_1250_ = v_messages_1225_;
goto v___jp_1249_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1309_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1220_, v___x_1312_, v___x_1313_, v_messages_1225_);
v___y_1250_ = v___x_1314_;
goto v___jp_1249_;
}
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1309_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1220_, v___x_1315_, v___x_1316_, v_messages_1225_);
v___y_1250_ = v___x_1317_;
goto v___jp_1249_;
}
}
v___jp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___boxed), 5, 2);
lean_closure_set(v___x_1247_, 0, v___x_1244_);
lean_closure_set(v___x_1247_, 1, v___y_1246_);
v___x_1248_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1247_, v_a_1208_, v_a_1209_);
return v___x_1248_;
}
v___jp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___y_1250_);
v___x_1252_ = v___x_1236_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_env_1224_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___y_1250_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_scopes_1226_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_usedQuotCtxts_1227_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1308_, 5, v_maxRecDepth_1229_);
lean_ctor_set(v_reuseFailAlloc_1308_, 6, v_ngen_1230_);
lean_ctor_set(v_reuseFailAlloc_1308_, 7, v_auxDeclNGen_1231_);
lean_ctor_set(v_reuseFailAlloc_1308_, 8, v_infoState_1232_);
lean_ctor_set(v_reuseFailAlloc_1308_, 9, v_traceState_1233_);
lean_ctor_set(v_reuseFailAlloc_1308_, 10, v_snapshotTasks_1234_);
v___x_1252_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1253_ = lean_st_ref_set(v_a_1209_, v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7);
lean_inc_n(v___x_1244_, 3);
v___x_1255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1244_);
lean_ctor_set(v___x_1255_, 1, v___x_1241_);
lean_ctor_set(v___x_1255_, 2, v___x_1254_);
v___x_1256_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10);
v___x_1257_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___x_1244_);
v___x_1258_ = l_Lean_Expr_app___override(v___x_1256_, v___x_1257_);
v___x_1259_ = lean_box(1);
v___x_1260_ = 1;
v___x_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1244_);
lean_ctor_set(v___x_1261_, 1, v___x_1241_);
v___x_1262_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1262_, 0, v___x_1255_);
lean_ctor_set(v___x_1262_, 1, v___x_1258_);
lean_ctor_set(v___x_1262_, 2, v___x_1259_);
lean_ctor_set(v___x_1262_, 3, v___x_1261_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*4, v___x_1260_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = lean_box(v___x_1212_);
v___x_1265_ = lean_box(v___x_1212_);
v___x_1266_ = lean_alloc_closure((void*)(l_Lean_addAndCompile___boxed), 6, 3);
lean_closure_set(v___x_1266_, 0, v___x_1263_);
lean_closure_set(v___x_1266_, 1, v___x_1264_);
lean_closure_set(v___x_1266_, 2, v___x_1265_);
v___x_1267_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1266_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_fileName_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec_ref_known(v___x_1267_, 1);
v_fileName_1268_ = lean_ctor_get(v_a_1208_, 0);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11));
v___x_1270_ = lean_string_append(v___x_1269_, v_fileName_1268_);
v___x_1271_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12));
v___x_1272_ = lean_string_append(v___x_1270_, v___x_1271_);
v___x_1273_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1242_, v___x_1212_);
v___x_1274_ = lean_string_append(v___x_1272_, v___x_1273_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13));
v___x_1276_ = lean_string_append(v___x_1274_, v___x_1275_);
v___x_1277_ = lean_string_append(v___x_1276_, v___x_1273_);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14));
v___x_1279_ = lean_string_append(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1279_, v___x_1273_);
lean_dec_ref(v___x_1273_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15));
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
lean_inc(v___x_1244_);
v___x_1283_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed), 5, 2);
lean_closure_set(v___x_1283_, 0, v___x_1244_);
lean_closure_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1283_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref_known(v___x_1284_, 1);
v___x_1285_ = l_Lean_Elab_Command_getRef___redArg(v_a_1208_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
lean_inc(v___x_1244_);
v___x_1287_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v___x_1244_, v_a_1286_, v_id_1240_, v_a_1208_, v_a_1209_);
lean_dec(v_a_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref_known(v___x_1287_, 1);
v___x_1288_ = lean_box(0);
lean_inc(v___x_1244_);
v___x_1289_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_id_1240_, v___x_1244_, v___x_1288_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
lean_dec_ref_known(v___x_1289_, 1);
v___x_1290_ = lean_array_get_size(v_a_1220_);
v___x_1291_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_1292_ = lean_nat_dec_lt(v___x_1238_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_dec(v_a_1220_);
v___y_1246_ = v___x_1291_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_nat_dec_le(v___x_1290_, v___x_1290_);
if (v___x_1293_ == 0)
{
if (v___x_1292_ == 0)
{
lean_dec(v_a_1220_);
v___y_1246_ = v___x_1291_;
goto v___jp_1245_;
}
else
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = lean_usize_of_nat(v___x_1290_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1220_, v___x_1294_, v___x_1295_, v___x_1291_);
lean_dec(v_a_1220_);
v___y_1246_ = v___x_1296_;
goto v___jp_1245_;
}
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1290_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1220_, v___x_1297_, v___x_1298_, v___x_1291_);
lean_dec(v_a_1220_);
v___y_1246_ = v___x_1299_;
goto v___jp_1245_;
}
}
}
else
{
lean_dec(v___x_1244_);
lean_dec(v_a_1220_);
return v___x_1289_;
}
}
else
{
lean_dec(v___x_1244_);
lean_dec(v_id_1240_);
lean_dec(v_a_1220_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v___x_1244_);
lean_dec(v_id_1240_);
lean_dec(v_a_1220_);
v_a_1300_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1285_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1285_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_dec(v___x_1244_);
lean_dec(v_id_1240_);
lean_dec(v_a_1220_);
return v___x_1284_;
}
}
else
{
lean_dec(v___x_1244_);
lean_dec(v___x_1242_);
lean_dec(v_id_1240_);
lean_dec(v_a_1220_);
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1216_);
lean_dec(v___x_1214_);
lean_dec(v_x_1207_);
v_a_1319_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1219_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1219_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v___x_1214_);
lean_dec(v_x_1207_);
v_a_1327_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1215_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1215_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___boxed(lean_object* v_x_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(v_x_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(lean_object* v_stx_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1340_, v___y_1341_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___boxed(lean_object* v_stx_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(v_stx_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v_stx_1345_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(lean_object* v_declName_1350_, lean_object* v_declRanges_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1350_, v_declRanges_1351_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___boxed(lean_object* v_declName_1356_, lean_object* v_declRanges_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(v_declName_1356_, v_declRanges_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(lean_object* v_t_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_1362_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___boxed(lean_object* v_t_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(v_t_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b1_1372_, lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_1373_, v___y_1374_, v___y_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1378_, lean_object* v_constName_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(v_00_u03b1_1378_, v_constName_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1384_, lean_object* v_ref_1385_, lean_object* v_constName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_1385_, v_constName_1386_, v___y_1387_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_ref_1392_, lean_object* v_constName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(v_00_u03b1_1391_, v_ref_1392_, v_constName_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v_ref_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(lean_object* v_00_u03b1_1398_, lean_object* v_ref_1399_, lean_object* v_msg_1400_, lean_object* v_declHint_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_1399_, v_msg_1400_, v_declHint_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_ref_1407_, lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(v_00_u03b1_1406_, v_ref_1407_, v_msg_1408_, v_declHint_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v_ref_1407_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_1414_, v_declHint_1415_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_1420_, lean_object* v_declHint_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(v_msg_1420_, v_declHint_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object* v_00_u03b1_1426_, lean_object* v_ref_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_1427_, v_msg_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_ref_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(v_00_u03b1_1433_, v_ref_1434_, v_msg_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v_ref_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(lean_object* v_msgData_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_1440_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msgData_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(v_msgData_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1450_, lean_object* v_msg_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(v_00_u03b1_1456_, v_msg_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(lean_object* v_msgData_1462_, lean_object* v_macroStack_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_1462_, v_macroStack_1463_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_msgData_1468_, lean_object* v_macroStack_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(v_msgData_1468_, v_macroStack_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
if (lean_obj_tag(v_a_1474_) == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = l_List_reverse___redArg(v_a_1475_);
return v___x_1476_;
}
else
{
lean_object* v_head_1477_; lean_object* v_tail_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1499_; 
v_head_1477_ = lean_ctor_get(v_a_1474_, 0);
v_tail_1478_ = lean_ctor_get(v_a_1474_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1480_ = v_a_1474_;
v_isShared_1481_ = v_isSharedCheck_1499_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_tail_1478_);
lean_inc(v_head_1477_);
lean_dec(v_a_1474_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1499_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_fst_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1497_; 
v_fst_1482_ = lean_ctor_get(v_head_1477_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_head_1477_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v_head_1477_, 1);
lean_dec(v_unused_1498_);
v___x_1484_ = v_head_1477_;
v_isShared_1485_ = v_isSharedCheck_1497_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_fst_1482_);
lean_dec(v_head_1477_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1497_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1486_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_1487_ = l_Lean_privateToUserName(v_fst_1482_);
v___x_1488_ = l_Lean_MessageData_ofName(v___x_1487_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 7);
lean_ctor_set(v___x_1484_, 1, v___x_1488_);
lean_ctor_set(v___x_1484_, 0, v___x_1486_);
v___x_1490_ = v___x_1484_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v___x_1486_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_a_1475_);
lean_ctor_set(v___x_1480_, 0, v___x_1491_);
v___x_1493_ = v___x_1480_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_a_1475_);
v___x_1493_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
v_a_1474_ = v_tail_1478_;
v_a_1475_ = v___x_1493_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0));
v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8));
v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11));
v___x_1519_ = l_Lean_MessageData_ofFormat(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(lean_object* v_id_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_box(0);
lean_inc(v_id_1523_);
v___x_1528_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_1528_, 0, v_id_1523_);
lean_closure_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1528_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1567_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1567_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1567_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v_env_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_st_ref_get(v_a_1525_);
v_env_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc_ref(v_env_1535_);
lean_dec(v___x_1534_);
v___x_1536_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_1535_, v_a_1530_);
lean_dec(v_a_1530_);
if (lean_obj_tag(v___x_1536_) == 1)
{
lean_object* v_val_1537_; lean_object* v___x_1539_; 
lean_dec(v_id_1523_);
v_val_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v___x_1536_, 1);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_val_1537_);
v___x_1539_ = v___x_1532_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_val_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
lean_object* v___x_1541_; lean_object* v___y_1543_; lean_object* v_env_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
lean_dec(v___x_1536_);
lean_del_object(v___x_1532_);
v___x_1541_ = lean_st_ref_get(v_a_1525_);
v_env_1557_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_env_1557_);
lean_dec(v___x_1541_);
v___x_1558_ = l_Lean_PostprocessTraces_allStoredTraces(v_env_1557_);
v___x_1559_ = lean_box(0);
v___x_1560_ = l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(v___x_1558_, v___x_1559_);
v___x_1561_ = l_List_isEmpty___redArg(v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9);
v___x_1563_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12);
v___x_1564_ = l_Lean_MessageData_joinSep(v___x_1560_, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___y_1543_ = v___x_1565_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1566_; 
lean_dec(v___x_1560_);
v___x_1566_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14);
v___y_1543_ = v___x_1566_;
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1544_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1);
v___x_1545_ = l_Lean_TSyntax_getId(v_id_1523_);
v___x_1546_ = l_Lean_MessageData_ofName(v___x_1545_);
lean_inc_ref(v___x_1546_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1544_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___y_1543_);
v___x_1551_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v___x_1546_);
v___x_1554_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_id_1523_, v___x_1555_, v_a_1524_, v_a_1525_);
lean_dec(v_id_1523_);
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_id_1523_);
v_a_1568_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1529_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1529_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___boxed(lean_object* v_id_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1576_, v_a_1577_, v_a_1578_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(uint8_t v_suppressElabErrors_1582_, lean_object* v_x_1583_){
_start:
{
if (lean_obj_tag(v_x_1583_) == 1)
{
lean_object* v_pre_1584_; 
v_pre_1584_ = lean_ctor_get(v_x_1583_, 0);
if (lean_obj_tag(v_pre_1584_) == 0)
{
lean_object* v_str_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_str_1585_ = lean_ctor_get(v_x_1583_, 1);
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0));
v___x_1587_ = lean_string_dec_eq(v_str_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
return v___x_1587_;
}
else
{
return v_suppressElabErrors_1582_;
}
}
else
{
uint8_t v___x_1588_; 
v___x_1588_ = 0;
return v___x_1588_;
}
}
else
{
uint8_t v___x_1589_; 
v___x_1589_ = 0;
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1590_, lean_object* v_x_1591_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1592_; uint8_t v_res_1593_; lean_object* v_r_1594_; 
v_suppressElabErrors_boxed_1592_ = lean_unbox(v_suppressElabErrors_1590_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(v_suppressElabErrors_boxed_1592_, v_x_1591_);
lean_dec(v_x_1591_);
v_r_1594_ = lean_box(v_res_1593_);
return v_r_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v_as_1597_, size_t v_sz_1598_, size_t v_i_1599_, lean_object* v_b_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_a_1605_; uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1599_, v_sz_1598_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_b_1600_);
return v___x_1610_;
}
else
{
lean_object* v_fileName_1611_; lean_object* v_fileMap_1612_; uint8_t v_suppressElabErrors_1613_; lean_object* v_a_1614_; lean_object* v_data_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___y_1620_; 
v_fileName_1611_ = lean_ctor_get(v___y_1601_, 0);
v_fileMap_1612_ = lean_ctor_get(v___y_1601_, 1);
v_suppressElabErrors_1613_ = lean_ctor_get_uint8(v___y_1601_, sizeof(void*)*10);
v_a_1614_ = lean_array_uget_borrowed(v_as_1597_, v_i_1599_);
v_data_1615_ = lean_ctor_get(v_a_1614_, 4);
v___x_1616_ = lean_box(0);
v___x_1617_ = 0;
lean_inc(v_data_1615_);
lean_inc_ref(v_fileMap_1612_);
lean_inc_ref(v_fileName_1611_);
v___x_1618_ = l_Lean_Elab_mkMessageCore(v_fileName_1611_, v_fileMap_1612_, v_data_1615_, v___x_1617_, v___y_1595_, v___y_1596_);
if (v_suppressElabErrors_1613_ == 0)
{
v___y_1620_ = v___y_1602_;
goto v___jp_1619_;
}
else
{
lean_object* v_data_1681_; lean_object* v___x_1682_; lean_object* v___f_1683_; uint8_t v___x_1684_; 
v_data_1681_ = lean_ctor_get(v___x_1618_, 4);
lean_inc(v_data_1681_);
v___x_1682_ = lean_box(v_suppressElabErrors_1613_);
v___f_1683_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1683_, 0, v___x_1682_);
v___x_1684_ = l_Lean_MessageData_hasTag(v___f_1683_, v_data_1681_);
if (v___x_1684_ == 0)
{
lean_dec_ref(v___x_1618_);
v_a_1605_ = v___x_1616_;
goto v___jp_1604_;
}
else
{
v___y_1620_ = v___y_1602_;
goto v___jp_1619_;
}
}
v___jp_1619_:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Elab_Command_getScope___redArg(v___y_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_Elab_Command_getScope___redArg(v___y_1620_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; lean_object* v_currNamespace_1626_; lean_object* v_openDecls_1627_; lean_object* v_fileName_1628_; lean_object* v_pos_1629_; lean_object* v_endPos_1630_; uint8_t v_keepFullRange_1631_; uint8_t v_severity_1632_; uint8_t v_isSilent_1633_; lean_object* v_caption_1634_; lean_object* v_data_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1664_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = lean_st_ref_take(v___y_1620_);
v_currNamespace_1626_ = lean_ctor_get(v_a_1622_, 2);
lean_inc(v_currNamespace_1626_);
lean_dec(v_a_1622_);
v_openDecls_1627_ = lean_ctor_get(v_a_1624_, 3);
lean_inc(v_openDecls_1627_);
lean_dec(v_a_1624_);
v_fileName_1628_ = lean_ctor_get(v___x_1618_, 0);
v_pos_1629_ = lean_ctor_get(v___x_1618_, 1);
v_endPos_1630_ = lean_ctor_get(v___x_1618_, 2);
v_keepFullRange_1631_ = lean_ctor_get_uint8(v___x_1618_, sizeof(void*)*5);
v_severity_1632_ = lean_ctor_get_uint8(v___x_1618_, sizeof(void*)*5 + 1);
v_isSilent_1633_ = lean_ctor_get_uint8(v___x_1618_, sizeof(void*)*5 + 2);
v_caption_1634_ = lean_ctor_get(v___x_1618_, 3);
v_data_1635_ = lean_ctor_get(v___x_1618_, 4);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1637_ = v___x_1618_;
v_isShared_1638_ = v_isSharedCheck_1664_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_data_1635_);
lean_inc(v_caption_1634_);
lean_inc(v_endPos_1630_);
lean_inc(v_pos_1629_);
lean_inc(v_fileName_1628_);
lean_dec(v___x_1618_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1664_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_env_1639_; lean_object* v_messages_1640_; lean_object* v_scopes_1641_; lean_object* v_usedQuotCtxts_1642_; lean_object* v_nextMacroScope_1643_; lean_object* v_maxRecDepth_1644_; lean_object* v_ngen_1645_; lean_object* v_auxDeclNGen_1646_; lean_object* v_infoState_1647_; lean_object* v_traceState_1648_; lean_object* v_snapshotTasks_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1663_; 
v_env_1639_ = lean_ctor_get(v___x_1625_, 0);
v_messages_1640_ = lean_ctor_get(v___x_1625_, 1);
v_scopes_1641_ = lean_ctor_get(v___x_1625_, 2);
v_usedQuotCtxts_1642_ = lean_ctor_get(v___x_1625_, 3);
v_nextMacroScope_1643_ = lean_ctor_get(v___x_1625_, 4);
v_maxRecDepth_1644_ = lean_ctor_get(v___x_1625_, 5);
v_ngen_1645_ = lean_ctor_get(v___x_1625_, 6);
v_auxDeclNGen_1646_ = lean_ctor_get(v___x_1625_, 7);
v_infoState_1647_ = lean_ctor_get(v___x_1625_, 8);
v_traceState_1648_ = lean_ctor_get(v___x_1625_, 9);
v_snapshotTasks_1649_ = lean_ctor_get(v___x_1625_, 10);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1651_ = v___x_1625_;
v_isShared_1652_ = v_isSharedCheck_1663_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_snapshotTasks_1649_);
lean_inc(v_traceState_1648_);
lean_inc(v_infoState_1647_);
lean_inc(v_auxDeclNGen_1646_);
lean_inc(v_ngen_1645_);
lean_inc(v_maxRecDepth_1644_);
lean_inc(v_nextMacroScope_1643_);
lean_inc(v_usedQuotCtxts_1642_);
lean_inc(v_scopes_1641_);
lean_inc(v_messages_1640_);
lean_inc(v_env_1639_);
lean_dec(v___x_1625_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1663_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_currNamespace_1626_);
lean_ctor_set(v___x_1653_, 1, v_openDecls_1627_);
v___x_1654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_data_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v___x_1654_);
v___x_1656_ = v___x_1637_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_fileName_1628_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_pos_1629_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_endPos_1630_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_caption_1634_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v___x_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*5, v_keepFullRange_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*5 + 1, v_severity_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*5 + 2, v_isSilent_1633_);
v___x_1656_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = l_Lean_MessageLog_add(v___x_1656_, v_messages_1640_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v___x_1657_);
v___x_1659_ = v___x_1651_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_env_1639_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_scopes_1641_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_usedQuotCtxts_1642_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_nextMacroScope_1643_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v_maxRecDepth_1644_);
lean_ctor_set(v_reuseFailAlloc_1661_, 6, v_ngen_1645_);
lean_ctor_set(v_reuseFailAlloc_1661_, 7, v_auxDeclNGen_1646_);
lean_ctor_set(v_reuseFailAlloc_1661_, 8, v_infoState_1647_);
lean_ctor_set(v_reuseFailAlloc_1661_, 9, v_traceState_1648_);
lean_ctor_set(v_reuseFailAlloc_1661_, 10, v_snapshotTasks_1649_);
v___x_1659_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_st_ref_set(v___y_1620_, v___x_1659_);
v_a_1605_ = v___x_1616_;
goto v___jp_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_a_1622_);
lean_dec_ref(v___x_1618_);
v_a_1665_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1623_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1623_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v___x_1618_);
v_a_1673_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1621_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1621_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
v___jp_1604_:
{
size_t v___x_1606_; size_t v___x_1607_; 
v___x_1606_ = ((size_t)1ULL);
v___x_1607_ = lean_usize_add(v_i_1599_, v___x_1606_);
v_i_1599_ = v___x_1607_;
v_b_1600_ = v_a_1605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___boxed(lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v_as_1687_, lean_object* v_sz_1688_, lean_object* v_i_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1688_);
lean_dec(v_sz_1688_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1689_);
lean_dec(v_i_1689_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1685_, v___y_1686_, v_as_1687_, v_sz_boxed_1694_, v_i_boxed_1695_, v_b_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v_as_1687_);
lean_dec(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(lean_object* v_x_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1));
lean_inc(v_x_1697_);
v___x_1702_ = l_Lean_Syntax_isOfKind(v_x_1697_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
lean_dec(v_x_1697_);
v___x_1703_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; lean_object* v_id_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_unsigned_to_nat(1u);
v_id_1705_ = l_Lean_Syntax_getArg(v_x_1697_, v___x_1704_);
v___x_1706_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1705_, v_a_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v_post_1709_; lean_object* v___x_1710_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = lean_unsigned_to_nat(2u);
v_post_1709_ = l_Lean_Syntax_getArg(v_x_1697_, v___x_1708_);
lean_dec(v_x_1697_);
v___x_1710_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1709_, v_a_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed), 5, 2);
lean_closure_set(v___x_1712_, 0, v_a_1707_);
lean_closure_set(v___x_1712_, 1, v_a_1711_);
v___x_1713_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1712_, v_a_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = l_Lean_Elab_Command_getRef___redArg(v_a_1698_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___y_1718_; lean_object* v___y_1719_; uint8_t v___x_1732_; lean_object* v___y_1734_; lean_object* v___x_1737_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___x_1732_ = 0;
v___x_1737_ = l_Lean_Syntax_getPos_x3f(v_a_1716_, v___x_1732_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___y_1734_ = v___x_1738_;
goto v___jp_1733_;
}
else
{
lean_object* v_val_1739_; 
v_val_1739_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_val_1739_);
lean_dec_ref_known(v___x_1737_, 1);
v___y_1734_ = v_val_1739_;
goto v___jp_1733_;
}
v___jp_1717_:
{
lean_object* v___x_1720_; size_t v_sz_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1720_ = lean_box(0);
v_sz_1721_ = lean_array_size(v_a_1714_);
v___x_1722_ = ((size_t)0ULL);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1718_, v___y_1719_, v_a_1714_, v_sz_1721_, v___x_1722_, v___x_1720_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1714_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v___x_1723_, 0);
lean_dec(v_unused_1731_);
v___x_1725_ = v___x_1723_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_dec(v___x_1723_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1720_);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1720_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
return v___x_1723_;
}
}
v___jp_1733_:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Syntax_getTailPos_x3f(v_a_1716_, v___x_1732_);
lean_dec(v_a_1716_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_inc(v___y_1734_);
v___y_1718_ = v___y_1734_;
v___y_1719_ = v___y_1734_;
goto v___jp_1717_;
}
else
{
lean_object* v_val_1736_; 
v_val_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___y_1718_ = v___y_1734_;
v___y_1719_ = v_val_1736_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1714_);
v_a_1740_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1715_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1715_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_a_1748_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1713_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1713_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1707_);
v_a_1756_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1710_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1710_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v_x_1697_);
v_a_1764_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1706_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1706_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces___boxed(lean_object* v_x_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(v_x_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
return v_res_1776_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PostprocessTraces_StoredTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PostprocessTraces_StoredTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PostprocessTraces_StoredTraces(builtin);
}
#ifdef __cplusplus
}
#endif
